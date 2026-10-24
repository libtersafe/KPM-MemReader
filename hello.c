/* SPDX-License-Identifier: GPL-2.0-or-later */
/*  * KPM 模块 
 * 开源作者: 小迷糊 @xmhnb
 * 描述: KPM hook ioctl 读写
 * 由 https://github.com/libtersafe 指导完成

 * Copyright (C) 2023 bmax121. All Rights Reserved.
 */


#include <compiler.h>
#include <kpmodule.h>
#include <linux/printk.h>
#include <common.h>
#include <syscall.h>


#define ENABLE_DEBUG_LOG 1

#if ENABLE_DEBUG_LOG
    #define TAG "[@xmhnb]"
    #define logv(fmt, ...) pr_info(TAG fmt, ##__VA_ARGS__)
#else
    #define logv(fmt, ...) do {} while(0) 
#endif


KPM_NAME("@xmhnb");
KPM_VERSION("1.0.0");
KPM_LICENSE("GPL v2");
KPM_AUTHOR("小迷糊开源官方群@xmhnb");
KPM_DESCRIPTION("小迷糊开源HOOK_ioctl内核模块");

/* ========== ioctl 命令定义 ========== */
#define OP_READ_MEM                 8001
#define OP_WRITE_MEM                8002 // ADDED FOR WRITE SUPPORT
#define OP_GET_CPU_NUM_BRPS         8009
#define OP_GET_CPU_NUM_WRPS         8010
#define OP_SET_HW_BREAKPOINT        8011
#define OP_REMOVE_HW_BREAKPOINT     8013
#define OP_REMOVE_ALL_HW_BREAKPOINT 8014


typedef struct {
    uint32_t pid;
    uint32_t _pad0;
    uint64_t addr;
    uint64_t buffer;
    uint64_t size;
} copy_memory_t;

typedef struct {
    uint32_t pid;
    uint32_t _pad0;
    uint64_t addr;
    int32_t  type;
    int32_t  _pad1;
    uint64_t len;
} hw_breakpoint_cmd_t;


struct bp_node {
    struct bp_node *next;
    struct bp_node *prev;
    uint64_t perf_event;
    uint32_t pid;
    uint32_t pad;
    uint64_t addr;
};


static uint64_t my_page_shift = 12;
static uint64_t my_va_bits = 48;
static uint64_t my_pa_bits = 48;


static struct bp_node bp_list = {
    .next = &bp_list,
    .prev = &bp_list,
};
static uint32_t bp_lock = 0;


static uint64_t kv_memstart_addr = 0;
static uint64_t kv_kimage_voffset = 0;
static uint64_t pgd_offset = 0;


static uint64_t (*kf___arch_copy_from_user)(void *to, const void __user *from, uint64_t n) = 0;
static uint64_t (*kf___arch_copy_to_user)(void __user *to, const void *from, uint64_t n) = 0;
static void *(*kf_get_task_pid)(void *task, int type) = 0;
static void (*kf_put_pid)(void *pid) = 0;
static void *(*kf_find_task_by_vpid)(uint32_t pid) = 0;
static volatile uint64_t kf_attach_pid = 0;
static void *(*kf_get_task_mm)(void *task) = 0;
static void (*kf_mmput)(void *mm) = 0;
static int (*kf_pfn_valid)(uint64_t pfn) = 0;
static int (*kf_valid_phys_addr_range)(uint64_t addr, uint64_t size) = 0;
static void *(*kf_register_user_hw_breakpoint)(void *attr, void *handler, void *overflow, void *task) = 0;
static volatile uint64_t kf_modify_user_hw_breakpoint = 0;
static void (*kf_unregister_hw_breakpoint)(void *event) = 0;
static void (*kf_perf_event_enable)(void *event) = 0;
static void *(*kf_memset)(void *s, int c, uint64_t n) = 0;
static void *(*kf___kmalloc)(uint64_t size, uint32_t flags) = 0;
static void *(*kf_kmalloc)(uint64_t size, uint32_t flags) = 0;
static void (*kf_kfree)(void *ptr) = 0;
static void (*kf__raw_spin_lock)(void *lock) = 0;
static void (*kf__raw_spin_unlock)(void *lock) = 0;


static const uint64_t pa_bits_table[] = { 32, 36, 40, 42, 44, 48, 52 };


#define LIST_POISON1  0xDEAD000000000100ULL
#define LIST_POISON2  0xDEAD000000000122ULL

static inline void bp_list_add(struct bp_node *node, struct bp_node *head)
{
    struct bp_node *old_next = head->next;
    head->next = node;
    node->next = (struct bp_node *)head;
    node->prev = old_next;
    old_next->next = node;
}

static inline void bp_list_del(struct bp_node *entry)
{
    struct bp_node *n = entry->next;
    struct bp_node *p = entry->prev;
    n->prev = p;
    p->next = n;
    entry->next = (struct bp_node *)LIST_POISON1;
    entry->prev = (struct bp_node *)LIST_POISON2;
}


uint64_t *pgtable_entry(uint64_t table_base, uint64_t va)
{
    uint64_t ps = my_page_shift;
    uint64_t vb = my_va_bits;
    uint64_t es = ps - 3;
    int64_t levels = (int64_t)((vb - 4) / es);
    uint64_t *result;

    if (levels < 1)
        return 0;

    int64_t level = 4 - levels;
    uint64_t pmask = ~(-1ULL << (48 - (uint8_t)ps)) << ps;
    uint64_t imask = (1U << es) - 1;

    while (1) {
        uint64_t shift = (4 - (uint8_t)level) * es + 3;
        uint64_t idx = (va >> shift) & imask;
        result = (uint64_t *)(table_base + idx * 8);
        uint64_t entry = *result;
        uint64_t dt = entry & 3;

        if (dt == 3) {
            table_base = (pmask & entry) + (-1ULL << vb) - *(uint64_t *)kv_memstart_addr;
            level++;
            if (level >= 3)
                return result;
        } else if (dt == 1) {
            if (level == 0) {
                pmask = ~(-1ULL << (48 - ((uint8_t)ps + 3 * es))) << ((uint8_t)ps + 3 * es);
                table_base = (pmask & entry) + (-1ULL << vb) - *(uint64_t *)kv_memstart_addr;
                level++;
                if (level >= 3)
                    return result;
                continue;
            }
            return result;
        } else {
            return 0;
        }
    }
}


static void hw_breakpoint_handler(void *event, void *data)
{
    logv("hw_breakpoint: Breakpoint hit\n");
}

static void before_ioctl(hook_fargs4_t *args, void *udata);


static long hello_demo_init(const char *args, const char *event, void *__user reserved)
{
    kv_memstart_addr = (uint64_t)kallsyms_lookup_name("memstart_addr");
    kv_kimage_voffset = (uint64_t)kallsyms_lookup_name("kimage_voffset");
    kf___arch_copy_from_user = (typeof(kf___arch_copy_from_user))kallsyms_lookup_name("__arch_copy_from_user");
    kf___arch_copy_to_user = (typeof(kf___arch_copy_to_user))kallsyms_lookup_name("__arch_copy_to_user");
    kf_get_task_pid = (typeof(kf_get_task_pid))kallsyms_lookup_name("get_task_pid");
    kf_put_pid = (typeof(kf_put_pid))kallsyms_lookup_name("put_pid");
    kf_find_task_by_vpid = (typeof(kf_find_task_by_vpid))kallsyms_lookup_name("find_task_by_vpid");
    kf_attach_pid = (uint64_t)kallsyms_lookup_name("attach_pid");
    kf_get_task_mm = (typeof(kf_get_task_mm))kallsyms_lookup_name("get_task_mm");
    kf_mmput = (typeof(kf_mmput))kallsyms_lookup_name("mmput");
    kf_pfn_valid = (typeof(kf_pfn_valid))kallsyms_lookup_name("pfn_valid");
    kf_valid_phys_addr_range = (typeof(kf_valid_phys_addr_range))kallsyms_lookup_name("valid_phys_addr_range");
    kf_register_user_hw_breakpoint = (typeof(kf_register_user_hw_breakpoint))kallsyms_lookup_name("register_user_hw_breakpoint");
    kf_modify_user_hw_breakpoint = (uint64_t)kallsyms_lookup_name("modify_user_hw_breakpoint");
    kf_unregister_hw_breakpoint = (typeof(kf_unregister_hw_breakpoint))kallsyms_lookup_name("unregister_hw_breakpoint");
    kf_perf_event_enable = (typeof(kf_perf_event_enable))kallsyms_lookup_name("perf_event_enable");
    kf_memset = (typeof(kf_memset))kallsyms_lookup_name("memset");
    kf___kmalloc = (typeof(kf___kmalloc))kallsyms_lookup_name("__kmalloc");
    kf_kmalloc = (typeof(kf_kmalloc))kallsyms_lookup_name("kmalloc");
    kf_kfree = (typeof(kf_kfree))kallsyms_lookup_name("kfree");
    kf__raw_spin_lock = (typeof(kf__raw_spin_lock))kallsyms_lookup_name("_raw_spin_lock");
    kf__raw_spin_unlock = (typeof(kf__raw_spin_unlock))kallsyms_lookup_name("_raw_spin_unlock");

    uint64_t tcr_el1;
    __asm__ volatile("mrs %0, tcr_el1" : "=r"(tcr_el1));
    uint64_t tg1 = (tcr_el1 >> 30) & 0x3;
    my_va_bits = 64 - ((tcr_el1 >> 16) & 0x1F);
    if (tg1 == 1)
        my_page_shift = 14;
    else if (tg1 == 3)
        my_page_shift = 16;
    else
        my_page_shift = 12;

    uint64_t mmfr0;
    __asm__ volatile("mrs %0, id_aa64mmfr0_el1" : "=r"(mmfr0));
    uint64_t parange = mmfr0 & 0xF;
    if (parange > 6)
        my_pa_bits = 48;
    else
        my_pa_bits = pa_bits_table[parange];

    uint64_t ttbr1;
    __asm__ volatile("mrs %0, ttbr1_el1" : "=r"(ttbr1));

    uint64_t init_mm_addr = (uint64_t)kallsyms_lookup_name("init_mm");
    if (init_mm_addr && init_mm_addr <= 0xFFFFFFFFFFFFFF4FULL) {
        uint64_t expected_pgd = *(uint64_t *)kv_kimage_voffset
                              + (ttbr1 & (-1ULL << my_page_shift) & 0xFFFFFFFFFFFEULL);
        uint64_t off;
        for (off = 0; off < 176; off += 4) {
            if (*(uint64_t *)(init_mm_addr + off) == expected_pgd) {
                pgd_offset = off;
                break;
            }
        }
    }

    uint64_t init_task_addr = (uint64_t)kallsyms_lookup_name("init_task");
    if (init_task_addr) {
        if (kf_get_task_pid) {
            void *pid = kf_get_task_pid((void *)init_task_addr, 0);
            if (kf_put_pid)
                kf_put_pid(pid);
        } else {
            logv("kfunc: %s not found\n", "get_task_pid");
        }
    }

    return (long)fp_wrap_syscalln(29, 3, 0, before_ioctl, 0, 0);
}


static long hello_demo_control0(const char *ctl_args, char *__user out_msg, int outlen)
{
    logv("welcome to use my kpm\n");
    return 0;
}


static long hello_demo_exit(void *__user reserved)
{
    fp_unwrap_syscalln(29, 0, before_ioctl, 0);

    kf__raw_spin_lock(&bp_lock);
    struct bp_node *pos = bp_list.next;
    while ((void *)pos != (void *)&bp_list) {
        struct bp_node *next_node = pos->next;
        bp_list_del(pos);
        if (kf_unregister_hw_breakpoint)
            kf_unregister_hw_breakpoint((void *)pos->perf_event);
        kf_kfree(pos);
        pos = next_node;
    }
    kf__raw_spin_unlock(&bp_lock);

    logv("hello_demo_exit\n");
    return 0;
}


static void before_ioctl(hook_fargs4_t *args, void *udata)
{
    uint64_t *regs = syscall_args(args);
    int64_t cmd = (int64_t)regs[1];
    uint64_t user_data = regs[2];

    if ((uint64_t)(cmd - OP_READ_MEM) > (uint64_t)(OP_REMOVE_ALL_HW_BREAKPOINT - OP_READ_MEM))
        return;

    if (cmd == OP_READ_MEM) {
        copy_memory_t rcmd;
        if (kf___arch_copy_from_user(&rcmd, (void __user *)user_data, sizeof(rcmd)))
            return;
        uint64_t remaining = rcmd.size;
        if (!remaining) return;
        uint64_t vaddr = rcmd.addr;
        uint64_t outbuf = rcmd.buffer;

        while (remaining) {
            uint64_t pgsz = 1ULL << my_page_shift;
            uint64_t pgoff = vaddr & (pgsz - 1);
            uint64_t chunk = pgsz - pgoff;
            if (chunk > remaining) chunk = remaining;

            void *task = kf_find_task_by_vpid(rcmd.pid);
            if (!task) goto next_chunk;
            void *mm = kf_get_task_mm(task);
            if (!mm) goto next_chunk;

            uint64_t ps = my_page_shift;
            uint64_t vb = my_va_bits;
            uint64_t es = ps - 3;
            int64_t levels = (int64_t)((vb - 4) / es);
            uint64_t phys_addr = 0;

            if (levels >= 1) {
                int64_t level = 4 - levels;
                uint64_t tbl = *(uint64_t *)((uint64_t)mm + pgd_offset);
                uint64_t pmask = ~(-1ULL << (48 - (uint8_t)ps)) << ps;
                uint64_t imask = (1U << es) - 1;
                int found = 0;

                while (!found) {
                    uint64_t shift = (4 - (uint8_t)level) * es + 3;
                    uint64_t idx = (vaddr >> shift) & imask;
                    uint64_t entry = *(uint64_t *)(tbl + idx * 8);
                    uint64_t dt = entry & 3;

                    if (dt == 3) {
                        tbl = (pmask & entry) + (-1ULL << vb) - *(uint64_t *)kv_memstart_addr;
                        level++;
                        if (level >= 3) { found = 1; break; }
                    } else if (dt == 1) {
                        if (level == 0) {
                            pmask = ~(-1ULL << (48 - ((uint8_t)ps + 3 * es))) << ((uint8_t)ps + 3 * es);
                            tbl = (pmask & entry) + (-1ULL << vb) - *(uint64_t *)kv_memstart_addr;
                            level++;
                            if (level >= 3) { found = 1; break; }
                            continue;
                        }
                        found = 1; break;
                    } else {
                        break;
                    }
                }

                if (found) {
                    uint64_t shift = (4 - (uint8_t)level) * es + 3;
                    uint64_t idx = (vaddr >> shift) & imask;
                    uint64_t entry = *(uint64_t *)(tbl + idx * 8);
                    if ((~(uint16_t)entry & 0x401) == 0) {
                        uint64_t pa_frame = 0;
                        if (my_pa_bits == 52)
                            pa_frame = (entry << 36) & 0xF000000000000ULL;
                        phys_addr = (pa_frame + (entry & pmask)) & (-1ULL << ps);
                        phys_addr |= vaddr & ~(-1ULL << ps);
                    }
                }
            }

            if (kf_mmput) kf_mmput(mm);

            if (phys_addr) {
                if (kf_pfn_valid(phys_addr >> my_page_shift) &&
                    kf_valid_phys_addr_range(phys_addr, chunk)) {
                    uint64_t kva = (phys_addr & (-1ULL << my_page_shift))
                                 - *(uint64_t *)kv_memstart_addr
                                 + (-1ULL << my_va_bits)
                                 + (phys_addr & ~(-1ULL << my_page_shift));
                    kf___arch_copy_to_user((void __user *)outbuf, (void *)kva, chunk);
                }
            }

        next_chunk:
            remaining -= chunk;
            vaddr += chunk;
            outbuf += chunk;
        }
        return;
    }

    // ==========================================
    // ADDED: OP_WRITE_MEM (8002) BLOCK
    // ==========================================
    if (cmd == OP_WRITE_MEM) {
        copy_memory_t rcmd;
        if (kf___arch_copy_from_user(&rcmd, (void __user *)user_data, sizeof(rcmd)))
            return;
        uint64_t remaining = rcmd.size;
        if (!remaining) return;
        uint64_t vaddr = rcmd.addr;
        uint64_t inbuf = rcmd.buffer;

        while (remaining) {
            uint64_t pgsz = 1ULL << my_page_shift;
            uint64_t pgoff = vaddr & (pgsz - 1);
            uint64_t chunk = pgsz - pgoff;
            if (chunk > remaining) chunk = remaining;

            void *task = kf_find_task_by_vpid(rcmd.pid);
            if (!task) goto next_chunk_w;
            void *mm = kf_get_task_mm(task);
            if (!mm) goto next_chunk_w;

            uint64_t ps = my_page_shift;
            uint64_t vb = my_va_bits;
            uint64_t es = ps - 3;
            int64_t levels = (int64_t)((vb - 4) / es);
            uint64_t phys_addr = 0;

            if (levels >= 1) {
                int64_t level = 4 - levels;
                uint64_t tbl = *(uint64_t *)((uint64_t)mm + pgd_offset);
                uint64_t pmask = ~(-1ULL << (48 - (uint8_t)ps)) << ps;
                uint64_t imask = (1U << es) - 1;
                int found = 0;

                while (!found) {
                    uint64_t shift = (4 - (uint8_t)level) * es + 3;
                    uint64_t idx = (vaddr >> shift) & imask;
                    uint64_t entry = *(uint64_t *)(tbl + idx * 8);
                    uint64_t dt = entry & 3;

                    if (dt == 3) {
                        tbl = (pmask & entry) + (-1ULL << vb) - *(uint64_t *)kv_memstart_addr;
                        level++;
                        if (level >= 3) { found = 1; break; }
                    } else if (dt == 1) {
                        if (level == 0) {
                            pmask = ~(-1ULL << (48 - ((uint8_t)ps + 3 * es))) << ((uint8_t)ps + 3 * es);
                            tbl = (pmask & entry) + (-1ULL << vb) - *(uint64_t *)kv_memstart_addr;
                            level++;
                            if (level >= 3) { found = 1; break; }
                            continue;
                        }
                        found = 1; break;
                    } else {
                        break;
                    }
                }

                if (found) {
                    uint64_t shift = (4 - (uint8_t)level) * es + 3;
                    uint64_t idx = (vaddr >> shift) & imask;
                    uint64_t entry = *(uint64_t *)(tbl + idx * 8);
                    if ((~(uint16_t)entry & 0x401) == 0) {
                        uint64_t pa_frame = 0;
                        if (my_pa_bits == 52)
                            pa_frame = (entry << 36) & 0xF000000000000ULL;
                        phys_addr = (pa_frame + (entry & pmask)) & (-1ULL << ps);
                        phys_addr |= vaddr & ~(-1ULL << ps);
                    }
                }
            }

            if (kf_mmput) kf_mmput(mm);

            if (phys_addr) {
                if (kf_pfn_valid(phys_addr >> my_page_shift) &&
                    kf_valid_phys_addr_range(phys_addr, chunk)) {
                    uint64_t kva = (phys_addr & (-1ULL << my_page_shift))
                                 - *(uint64_t *)kv_memstart_addr
                                 + (-1ULL << my_va_bits)
                                 + (phys_addr & ~(-1ULL << my_page_shift));
                    
                    // Write into kernel memory from user buffer
                    kf___arch_copy_from_user((void *)kva, (void __user *)inbuf, chunk);
                }
            }

        next_chunk_w:
            remaining -= chunk;
            vaddr += chunk;
            inbuf += chunk;
        }
        return;
    }

    if (cmd == OP_GET_CPU_NUM_BRPS || cmd == OP_GET_CPU_NUM_WRPS) {
        uint64_t __attribute__((unused)) dfr0;
        __asm__ volatile("mrs %0, id_aa64dfr0_el1" : "=r"(dfr0));
        return;
    }

    if (cmd == OP_SET_HW_BREAKPOINT) {
        hw_breakpoint_cmd_t bcmd;
        if (kf___arch_copy_from_user(&bcmd, (void __user *)user_data, sizeof(bcmd)))
            return;

        void *task = kf_find_task_by_vpid(bcmd.pid);
        if (!task) return;

        char attr[136];
        if (kf_memset) kf_memset(attr, 0, sizeof(attr));

        *(uint32_t *)(attr + 0x00) = 5;
        if (kver >> 9 >= 0x285) {
            *(uint32_t *)(attr + 0x04) = 120;
            if (kver > 0x50EFF) {
                *(uint32_t *)(attr + 0x04) = (kver >> 8 > 0x600) ? 136 : 128;
            }
        }
        *(uint64_t *)(attr + 0x10) = 1;
        *(uint64_t *)(attr + 0x28) |= 0x24;
        *(uint32_t *)(attr + 0x34) = bcmd.type;
        *(uint64_t *)(attr + 0x38) = bcmd.addr;
        *(uint64_t *)(attr + 0x40) = bcmd.len;

        void *ev = kf_register_user_hw_breakpoint(attr, hw_breakpoint_handler, 0, task);
        if ((uint64_t)ev > 0xFFFFFFFFFFFFF000ULL) return;

        if (kf_perf_event_enable) kf_perf_event_enable(ev);

        void *(*alloc_fn)(uint64_t, uint32_t);
        alloc_fn = kf_kmalloc ? (void *)kf_kmalloc : (void *)kf___kmalloc;
        struct bp_node *node = (struct bp_node *)alloc_fn(sizeof(struct bp_node), 0xD0);
        if (!node) {
            if (kf_unregister_hw_breakpoint) kf_unregister_hw_breakpoint(ev);
            return;
        }

        node->pid = bcmd.pid;
        node->perf_event = (uint64_t)ev;
        node->addr = bcmd.addr;

        kf__raw_spin_lock(&bp_lock);
        bp_list_add(node, &bp_list);
        kf__raw_spin_unlock(&bp_lock);
        return;
    }

    if (cmd == OP_REMOVE_HW_BREAKPOINT) {
        hw_breakpoint_cmd_t bcmd;
        if (kf___arch_copy_from_user(&bcmd, (void __user *)user_data, sizeof(bcmd)))
            return;

        kf__raw_spin_lock(&bp_lock);
        struct bp_node *pos = bp_list.next;
        while ((void *)pos != (void *)&bp_list) {
            struct bp_node *n = pos->next;
            if (pos->pid == bcmd.pid && pos->addr == bcmd.addr) {
                bp_list_del(pos);
                if (kf_unregister_hw_breakpoint)
                    kf_unregister_hw_breakpoint((void *)pos->perf_event);
                kf_kfree(pos);
                break;
            }
            pos = n;
        }
        kf__raw_spin_unlock(&bp_lock);
        return;
    }

    if (cmd == OP_REMOVE_ALL_HW_BREAKPOINT) {
        kf__raw_spin_lock(&bp_lock);
        struct bp_node *pos = bp_list.next;
        while ((void *)pos != (void *)&bp_list) {
            struct bp_node *n = pos->next;
            bp_list_del(pos);
            if (kf_unregister_hw_breakpoint)
                kf_unregister_hw_breakpoint((void *)pos->perf_event);
            kf_kfree(pos);
            pos = n;
        }
        kf__raw_spin_unlock(&bp_lock);
        return;
    }
}

KPM_INIT(hello_demo_init);
KPM_CTL0(hello_demo_control0);
KPM_EXIT(hello_demo_exit);
