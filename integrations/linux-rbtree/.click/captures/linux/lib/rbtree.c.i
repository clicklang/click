# 0 "lib/rbtree.c"
# 0 "<built-in>"
# 0 "<command-line>"
# 1 "././include/linux/compiler-version.h" 1
# 0 "<command-line>" 2
# 1 "././include/linux/kconfig.h" 1




# 1 "./include/generated/autoconf.h" 1
# 6 "././include/linux/kconfig.h" 2
# 0 "<command-line>" 2
# 1 "././include/linux/compiler_types.h" 1
# 89 "././include/linux/compiler_types.h"
# 1 "./include/linux/compiler_attributes.h" 1
# 90 "././include/linux/compiler_types.h" 2
# 151 "././include/linux/compiler_types.h"
# 1 "./include/linux/compiler-gcc.h" 1
# 152 "././include/linux/compiler_types.h" 2
# 168 "././include/linux/compiler_types.h"
struct ftrace_branch_data {
 const char *func;
 const char *file;
 unsigned line;
 union {
  struct {
   unsigned long correct;
   unsigned long incorrect;
  };
  struct {
   unsigned long miss;
   unsigned long hit;
  };
  unsigned long miss_hit[2];
 };
};

struct ftrace_likely_data {
 struct ftrace_branch_data data;
 unsigned long constant;
};
# 0 "<command-line>" 2
# 1 "lib/rbtree.c"
# 12 "lib/rbtree.c"
# 1 "./include/linux/rbtree_augmented.h" 1
# 15 "./include/linux/rbtree_augmented.h"
# 1 "./include/linux/compiler.h" 1




# 1 "./include/linux/compiler_types.h" 1
# 6 "./include/linux/compiler.h" 2
# 15 "./include/linux/compiler.h"
void ftrace_likely_update(struct ftrace_likely_data *f, int val,
     int expect, int is_constant);
# 220 "./include/linux/compiler.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void *offset_to_ptr(const int *off)
{
 return (void *)((unsigned long)off + *off);
}
# 251 "./include/linux/compiler.h"
# 1 "./arch/x86/include/generated/asm/rwonce.h" 1
# 1 "./include/asm-generic/rwonce.h" 1
# 26 "./include/asm-generic/rwonce.h"
# 1 "./include/linux/kasan-checks.h" 1




# 1 "./include/linux/types.h" 1





# 1 "./include/uapi/linux/types.h" 1




# 1 "./arch/x86/include/generated/uapi/asm/types.h" 1
# 1 "./include/uapi/asm-generic/types.h" 1






# 1 "./include/asm-generic/int-ll64.h" 1
# 11 "./include/asm-generic/int-ll64.h"
# 1 "./include/uapi/asm-generic/int-ll64.h" 1
# 12 "./include/uapi/asm-generic/int-ll64.h"
# 1 "./arch/x86/include/uapi/asm/bitsperlong.h" 1
# 11 "./arch/x86/include/uapi/asm/bitsperlong.h"
# 1 "./include/asm-generic/bitsperlong.h" 1




# 1 "./include/uapi/asm-generic/bitsperlong.h" 1
# 6 "./include/asm-generic/bitsperlong.h" 2
# 12 "./arch/x86/include/uapi/asm/bitsperlong.h" 2
# 13 "./include/uapi/asm-generic/int-ll64.h" 2







typedef __signed__ char __s8;
typedef unsigned char __u8;

typedef __signed__ short __s16;
typedef unsigned short __u16;

typedef __signed__ int __s32;
typedef unsigned int __u32;


__extension__ typedef __signed__ long long __s64;
__extension__ typedef unsigned long long __u64;
# 12 "./include/asm-generic/int-ll64.h" 2




typedef __s8 s8;
typedef __u8 u8;
typedef __s16 s16;
typedef __u16 u16;
typedef __s32 s32;
typedef __u32 u32;
typedef __s64 s64;
typedef __u64 u64;
# 8 "./include/uapi/asm-generic/types.h" 2
# 2 "./arch/x86/include/generated/uapi/asm/types.h" 2
# 6 "./include/uapi/linux/types.h" 2
# 14 "./include/uapi/linux/types.h"
# 1 "./include/uapi/linux/posix_types.h" 1




# 1 "./include/linux/stddef.h" 1




# 1 "./include/uapi/linux/stddef.h" 1
# 6 "./include/linux/stddef.h" 2




enum {
 false = 0,
 true = 1
};
# 6 "./include/uapi/linux/posix_types.h" 2
# 25 "./include/uapi/linux/posix_types.h"
typedef struct {
 unsigned long fds_bits[1024 / (8 * sizeof(long))];
} __kernel_fd_set;


typedef void (*__kernel_sighandler_t)(int);


typedef int __kernel_key_t;
typedef int __kernel_mqd_t;

# 1 "./arch/x86/include/asm/posix_types.h" 1




# 1 "./arch/x86/include/uapi/asm/posix_types_64.h" 1
# 11 "./arch/x86/include/uapi/asm/posix_types_64.h"
typedef unsigned short __kernel_old_uid_t;
typedef unsigned short __kernel_old_gid_t;


typedef unsigned long __kernel_old_dev_t;


# 1 "./include/uapi/asm-generic/posix_types.h" 1
# 15 "./include/uapi/asm-generic/posix_types.h"
typedef long __kernel_long_t;
typedef unsigned long __kernel_ulong_t;



typedef __kernel_ulong_t __kernel_ino_t;



typedef unsigned int __kernel_mode_t;



typedef int __kernel_pid_t;



typedef int __kernel_ipc_pid_t;



typedef unsigned int __kernel_uid_t;
typedef unsigned int __kernel_gid_t;



typedef __kernel_long_t __kernel_suseconds_t;



typedef int __kernel_daddr_t;



typedef unsigned int __kernel_uid32_t;
typedef unsigned int __kernel_gid32_t;
# 72 "./include/uapi/asm-generic/posix_types.h"
typedef __kernel_ulong_t __kernel_size_t;
typedef __kernel_long_t __kernel_ssize_t;
typedef __kernel_long_t __kernel_ptrdiff_t;




typedef struct {
 int val[2];
} __kernel_fsid_t;





typedef __kernel_long_t __kernel_off_t;
typedef long long __kernel_loff_t;
typedef __kernel_long_t __kernel_old_time_t;



typedef long long __kernel_time64_t;
typedef __kernel_long_t __kernel_clock_t;
typedef int __kernel_timer_t;
typedef int __kernel_clockid_t;
typedef char * __kernel_caddr_t;
typedef unsigned short __kernel_uid16_t;
typedef unsigned short __kernel_gid16_t;
# 19 "./arch/x86/include/uapi/asm/posix_types_64.h" 2
# 6 "./arch/x86/include/asm/posix_types.h" 2
# 37 "./include/uapi/linux/posix_types.h" 2
# 15 "./include/uapi/linux/types.h" 2


typedef __signed__ __int128 __s128 __attribute__((aligned(16)));
typedef unsigned __int128 __u128 __attribute__((aligned(16)));
# 36 "./include/uapi/linux/types.h"
typedef __u16 __le16;
typedef __u16 __be16;
typedef __u32 __le32;
typedef __u32 __be32;
typedef __u64 __le64;
typedef __u64 __be64;

typedef __u16 __sum16;
typedef __u32 __wsum;
# 59 "./include/uapi/linux/types.h"
typedef unsigned __poll_t;
# 7 "./include/linux/types.h" 2







typedef __s128 s128;
typedef __u128 u128;


typedef u32 __kernel_dev_t;

typedef __kernel_fd_set fd_set;
typedef __kernel_dev_t dev_t;
typedef __kernel_ulong_t ino_t;
typedef __kernel_mode_t mode_t;
typedef unsigned short umode_t;
typedef u32 nlink_t;
typedef __kernel_off_t off_t;
typedef __kernel_pid_t pid_t;
typedef __kernel_daddr_t daddr_t;
typedef __kernel_key_t key_t;
typedef __kernel_suseconds_t suseconds_t;
typedef __kernel_timer_t timer_t;
typedef __kernel_clockid_t clockid_t;
typedef __kernel_mqd_t mqd_t;

typedef _Bool bool;

typedef __kernel_uid32_t uid_t;
typedef __kernel_gid32_t gid_t;
typedef __kernel_uid16_t uid16_t;
typedef __kernel_gid16_t gid16_t;

typedef unsigned long uintptr_t;
typedef long intptr_t;



typedef __kernel_old_uid_t old_uid_t;
typedef __kernel_old_gid_t old_gid_t;



typedef __kernel_loff_t loff_t;
# 61 "./include/linux/types.h"
typedef __kernel_size_t size_t;




typedef __kernel_ssize_t ssize_t;




typedef __kernel_ptrdiff_t ptrdiff_t;




typedef __kernel_clock_t clock_t;




typedef __kernel_caddr_t caddr_t;



typedef unsigned char u_char;
typedef unsigned short u_short;
typedef unsigned int u_int;
typedef unsigned long u_long;


typedef unsigned char unchar;
typedef unsigned short ushort;
typedef unsigned int uint;
typedef unsigned long ulong;




typedef u8 u_int8_t;
typedef s8 int8_t;
typedef u16 u_int16_t;
typedef s16 int16_t;
typedef u32 u_int32_t;
typedef s32 int32_t;



typedef u8 uint8_t;
typedef u16 uint16_t;
typedef u32 uint32_t;


typedef u64 uint64_t;
typedef u64 u_int64_t;
typedef s64 int64_t;
# 124 "./include/linux/types.h"
typedef s64 ktime_t;
# 134 "./include/linux/types.h"
typedef u64 sector_t;
typedef u64 blkcnt_t;
# 152 "./include/linux/types.h"
typedef u64 dma_addr_t;




typedef unsigned int gfp_t;
typedef unsigned int slab_flags_t;
typedef unsigned int fmode_t;


typedef u64 phys_addr_t;




typedef phys_addr_t resource_size_t;





typedef unsigned long irq_hw_number_t;

typedef struct {
 int counter;
} atomic_t;




typedef struct {
 s64 counter;
} atomic64_t;


typedef struct {
 atomic_t refcnt;
} rcuref_t;



struct list_head {
 struct list_head *next, *prev;
};

struct hlist_head {
 struct hlist_node *first;
};

struct hlist_node {
 struct hlist_node *next, **pprev;
};

struct ustat {
 __kernel_daddr_t f_tfree;



 unsigned long f_tinode;

 char f_fname[6];
 char f_fpack[6];
};
# 235 "./include/linux/types.h"
struct callback_head {
 struct callback_head *next;
 void (*func)(struct callback_head *head);
} __attribute__((aligned(sizeof(void *))));


typedef void (*rcu_callback_t)(struct callback_head *head);
typedef void (*call_rcu_func_t)(struct callback_head *head, rcu_callback_t func);

typedef void (*swap_r_func_t)(void *a, void *b, int size, const void *priv);
typedef void (*swap_func_t)(void *a, void *b, int size);

typedef int (*cmp_r_func_t)(const void *a, const void *b, const void *priv);
typedef int (*cmp_func_t)(const void *a, const void *b);
# 6 "./include/linux/kasan-checks.h" 2
# 22 "./include/linux/kasan-checks.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) bool __kasan_check_read(const volatile void *p, unsigned int size)
{
 return true;
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) bool __kasan_check_write(const volatile void *p, unsigned int size)
{
 return true;
}
# 40 "./include/linux/kasan-checks.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) bool kasan_check_read(const volatile void *p, unsigned int size)
{
 return true;
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) bool kasan_check_write(const volatile void *p, unsigned int size)
{
 return true;
}
# 27 "./include/asm-generic/rwonce.h" 2
# 1 "./include/linux/kcsan-checks.h" 1
# 189 "./include/linux/kcsan-checks.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void __kcsan_check_access(const volatile void *ptr, size_t size,
     int type) { }

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void __kcsan_mb(void) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void __kcsan_wmb(void) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void __kcsan_rmb(void) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void __kcsan_release(void) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void kcsan_disable_current(void) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void kcsan_enable_current(void) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void kcsan_enable_current_nowarn(void) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void kcsan_nestable_atomic_begin(void) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void kcsan_nestable_atomic_end(void) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void kcsan_flat_atomic_begin(void) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void kcsan_flat_atomic_end(void) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void kcsan_atomic_next(int n) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void kcsan_set_access_mask(unsigned long mask) { }

struct kcsan_scoped_access { };

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) struct kcsan_scoped_access *
kcsan_begin_scoped_access(const volatile void *ptr, size_t size, int type,
     struct kcsan_scoped_access *sa) { return sa; }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void kcsan_end_scoped_access(struct kcsan_scoped_access *sa) { }
# 229 "./include/linux/kcsan-checks.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void kcsan_check_access(const volatile void *ptr, size_t size,
          int type) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void __kcsan_enable_current(void) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void __kcsan_disable_current(void) { }
# 28 "./include/asm-generic/rwonce.h" 2
# 64 "./include/asm-generic/rwonce.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__))
unsigned long __read_once_word_nocheck(const void *addr)
{
 return (*(const volatile typeof( _Generic((*(unsigned long *)addr), char: (char)0, unsigned char: (unsigned char)0, signed char: (signed char)0, unsigned short: (unsigned short)0, signed short: (signed short)0, unsigned int: (unsigned int)0, signed int: (signed int)0, unsigned long: (unsigned long)0, signed long: (signed long)0, unsigned long long: (unsigned long long)0, signed long long: (signed long long)0, default: (*(unsigned long *)addr))) *)&(*(unsigned long *)addr));
}
# 82 "./include/asm-generic/rwonce.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__))
unsigned long read_word_at_a_time(const void *addr)
{
 kasan_check_read(addr, 1);
 return *(unsigned long *)addr;
}
# 2 "./arch/x86/include/generated/asm/rwonce.h" 2
# 252 "./include/linux/compiler.h" 2
# 16 "./include/linux/rbtree_augmented.h" 2
# 1 "./include/linux/rbtree.h" 1
# 20 "./include/linux/rbtree.h"
# 1 "./include/linux/container_of.h" 1




# 1 "./include/linux/build_bug.h" 1
# 6 "./include/linux/container_of.h" 2
# 21 "./include/linux/rbtree.h" 2
# 1 "./include/linux/rbtree_types.h" 1




struct rb_node {
 unsigned long __rb_parent_color;
 struct rb_node *rb_right;
 struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));


struct rb_root {
 struct rb_node *rb_node;
};
# 26 "./include/linux/rbtree_types.h"
struct rb_root_cached {
 struct rb_root rb_root;
 struct rb_node *rb_leftmost;
};
# 22 "./include/linux/rbtree.h" 2


# 1 "./include/linux/rcupdate.h" 1
# 25 "./include/linux/rcupdate.h"
# 1 "./include/linux/atomic.h" 1






# 1 "./arch/x86/include/asm/atomic.h" 1






# 1 "./arch/x86/include/asm/alternative.h" 1





# 1 "./include/linux/stringify.h" 1
# 7 "./arch/x86/include/asm/alternative.h" 2
# 1 "./arch/x86/include/asm/asm.h" 1
# 118 "./arch/x86/include/asm/asm.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) __attribute__((__pure__)) void *rip_rel_ptr(void *p)
{
 asm("leaq %c1(%%rip), %0" : "=r"(p) : "i"(p));

 return p;
}
# 144 "./arch/x86/include/asm/asm.h"
# 1 "./arch/x86/include/asm/extable_fixup_types.h" 1
# 145 "./arch/x86/include/asm/asm.h" 2
# 222 "./arch/x86/include/asm/asm.h"
register unsigned long current_stack_pointer asm("rsp");
# 8 "./arch/x86/include/asm/alternative.h" 2
# 76 "./arch/x86/include/asm/alternative.h"
struct alt_instr {
 s32 instr_offset;
 s32 repl_offset;

 union {
  struct {
   u32 cpuid: 16;
   u32 flags: 16;
  };
  u32 ft_flags;
 };

 u8 instrlen;
 u8 replacementlen;
} __attribute__((__packed__));

extern struct alt_instr __alt_instructions[], __alt_instructions_end[];





extern int alternatives_patched;

extern void alternative_instructions(void);
extern void apply_alternatives(struct alt_instr *start, struct alt_instr *end);
extern void apply_retpolines(s32 *start, s32 *end);
extern void apply_returns(s32 *start, s32 *end);
extern void apply_seal_endbr(s32 *start, s32 *end);
extern void apply_fineibt(s32 *start_retpoline, s32 *end_retpoine,
     s32 *start_cfi, s32 *end_cfi);

struct module;

struct callthunk_sites {
 s32 *call_start, *call_end;
 struct alt_instr *alt_start, *alt_end;
};


extern void callthunks_patch_builtin_calls(void);
extern void callthunks_patch_module_calls(struct callthunk_sites *sites,
       struct module *mod);
extern void *callthunks_translate_call_dest(void *dest);
extern int x86_call_depth_emit_accounting(u8 **pprog, void *func);
# 138 "./arch/x86/include/asm/alternative.h"
extern void alternatives_smp_module_add(struct module *mod, char *name,
     void *locks, void *locks_end,
     void *text, void *text_end);
extern void alternatives_smp_module_del(struct module *mod);
extern void alternatives_enable_smp(void);
extern int alternatives_text_reserved(void *start, void *end);
extern bool skip_smp_alternatives;
# 352 "./arch/x86/include/asm/alternative.h"
void BUG_func(void);
void nop_func(void);
# 8 "./arch/x86/include/asm/atomic.h" 2
# 1 "./arch/x86/include/asm/cmpxchg.h" 1





# 1 "./arch/x86/include/asm/cpufeatures.h" 1





# 1 "./arch/x86/include/asm/required-features.h" 1
# 7 "./arch/x86/include/asm/cpufeatures.h" 2



# 1 "./arch/x86/include/asm/disabled-features.h" 1
# 11 "./arch/x86/include/asm/cpufeatures.h" 2
# 7 "./arch/x86/include/asm/cmpxchg.h" 2






extern void __xchg_wrong_size(void)
 __attribute__((__error__("Bad argument size for xchg")));
extern void __cmpxchg_wrong_size(void)
 __attribute__((__error__("Bad argument size for cmpxchg")));
extern void __xadd_wrong_size(void)
 __attribute__((__error__("Bad argument size for xadd")));
extern void __add_wrong_size(void)
 __attribute__((__error__("Bad argument size for add")));
# 145 "./arch/x86/include/asm/cmpxchg.h"
# 1 "./arch/x86/include/asm/cmpxchg_64.h" 1
# 23 "./arch/x86/include/asm/cmpxchg_64.h"
union __u128_halves {
 u128 full;
 struct {
  u64 low, high;
 };
};
# 44 "./arch/x86/include/asm/cmpxchg_64.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) u128 arch_cmpxchg128(volatile u128 *ptr, u128 old, u128 new)
{
 return ({ union __u128_halves o = { .full = (old), }, n = { .full = (new), }; asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchg16b %[ptr]" : [ptr] "+m" (*(ptr)), "+a" (o.low), "+d" (o.high) : "b" (n.low), "c" (n.high) : "memory"); o.full; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) u128 arch_cmpxchg128_local(volatile u128 *ptr, u128 old, u128 new)
{
 return ({ union __u128_halves o = { .full = (old), }, n = { .full = (new), }; asm volatile( "cmpxchg16b %[ptr]" : [ptr] "+m" (*(ptr)), "+a" (o.low), "+d" (o.high) : "b" (n.low), "c" (n.high) : "memory"); o.full; });
}
# 76 "./arch/x86/include/asm/cmpxchg_64.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool arch_try_cmpxchg128(volatile u128 *ptr, u128 *oldp, u128 new)
{
 return ({ union __u128_halves o = { .full = *(oldp), }, n = { .full = (new), }; bool ret; asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchg16b %[ptr]" "\n\t/* output condition code " "e" "*/\n" : "=@cc" "e" (ret), [ptr] "+m" (*(ptr)), "+a" (o.low), "+d" (o.high) : "b" (n.low), "c" (n.high) : "memory"); if (__builtin_expect(!!(!ret), 0)) *(oldp) = o.full; __builtin_expect(!!(ret), 1); });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool arch_try_cmpxchg128_local(volatile u128 *ptr, u128 *oldp, u128 new)
{
 return ({ union __u128_halves o = { .full = *(oldp), }, n = { .full = (new), }; bool ret; asm volatile( "cmpxchg16b %[ptr]" "\n\t/* output condition code " "e" "*/\n" : "=@cc" "e" (ret), [ptr] "+m" (*(ptr)), "+a" (o.low), "+d" (o.high) : "b" (n.low), "c" (n.high) : "memory"); if (__builtin_expect(!!(!ret), 0)) *(oldp) = o.full; __builtin_expect(!!(ret), 1); });
}
# 146 "./arch/x86/include/asm/cmpxchg.h" 2
# 9 "./arch/x86/include/asm/atomic.h" 2
# 1 "./arch/x86/include/asm/rmwcc.h" 1




# 1 "./include/linux/args.h" 1
# 6 "./arch/x86/include/asm/rmwcc.h" 2
# 10 "./arch/x86/include/asm/atomic.h" 2
# 1 "./arch/x86/include/asm/barrier.h" 1





# 1 "./arch/x86/include/asm/nops.h" 1
# 86 "./arch/x86/include/asm/nops.h"
extern const unsigned char * const x86_nops[];
# 7 "./arch/x86/include/asm/barrier.h" 2
# 36 "./arch/x86/include/asm/barrier.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) unsigned long array_index_mask_nospec(unsigned long index,
  unsigned long size)
{
 unsigned long mask;

 asm volatile ("cmp %1,%2; sbb %0,%0;"
   :"=r" (mask)
   :"g"(size),"r" (index)
   :"cc");
 return mask;
}
# 85 "./arch/x86/include/asm/barrier.h"
# 1 "./include/asm-generic/barrier.h" 1
# 18 "./include/asm-generic/barrier.h"
# 1 "./arch/x86/include/generated/asm/rwonce.h" 1
# 19 "./include/asm-generic/barrier.h" 2
# 86 "./arch/x86/include/asm/barrier.h" 2
# 11 "./arch/x86/include/asm/atomic.h" 2






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int arch_atomic_read(const atomic_t *v)
{




 return (*(const volatile typeof( _Generic(((v)->counter), char: (char)0, unsigned char: (unsigned char)0, signed char: (signed char)0, unsigned short: (unsigned short)0, signed short: (signed short)0, unsigned int: (unsigned int)0, signed int: (signed int)0, unsigned long: (unsigned long)0, signed long: (signed long)0, unsigned long long: (unsigned long long)0, signed long long: (signed long long)0, default: ((v)->counter))) *)&((v)->counter));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void arch_atomic_set(atomic_t *v, int i)
{
 do { *(volatile typeof(v->counter) *)&(v->counter) = (i); } while (0);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void arch_atomic_add(int i, atomic_t *v)
{
 asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "addl %1,%0"
       : "+m" (v->counter)
       : "ir" (i) : "memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void arch_atomic_sub(int i, atomic_t *v)
{
 asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "subl %1,%0"
       : "+m" (v->counter)
       : "ir" (i) : "memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool arch_atomic_sub_and_test(int i, atomic_t *v)
{
 return ({ bool c; asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "subl" " %[val], " "%[var]" "\n\t/* output condition code " "e" "*/\n" : [var] "+m" (v->counter), "=@cc" "e" (c) : [val] "er" (i) : "memory"); c; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void arch_atomic_inc(atomic_t *v)
{
 asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "incl %0"
       : "+m" (v->counter) :: "memory");
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void arch_atomic_dec(atomic_t *v)
{
 asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "decl %0"
       : "+m" (v->counter) :: "memory");
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool arch_atomic_dec_and_test(atomic_t *v)
{
 return ({ bool c; asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "decl" " " "%[var]" "\n\t/* output condition code " "e" "*/\n" : [var] "+m" (v->counter), "=@cc" "e" (c) : : "memory"); c; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool arch_atomic_inc_and_test(atomic_t *v)
{
 return ({ bool c; asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "incl" " " "%[var]" "\n\t/* output condition code " "e" "*/\n" : [var] "+m" (v->counter), "=@cc" "e" (c) : : "memory"); c; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool arch_atomic_add_negative(int i, atomic_t *v)
{
 return ({ bool c; asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "addl" " %[val], " "%[var]" "\n\t/* output condition code " "s" "*/\n" : [var] "+m" (v->counter), "=@cc" "s" (c) : [val] "er" (i) : "memory"); c; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int arch_atomic_add_return(int i, atomic_t *v)
{
 return i + ({ __typeof__ (*(((&v->counter)))) __ret = (((i))); switch (sizeof(*(((&v->counter))))) { case 1: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "b %b0, %1\n" : "+q" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 2: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "w %w0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 4: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "l %0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 8: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "q %q0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; default: __xadd_wrong_size(); } __ret; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int arch_atomic_sub_return(int i, atomic_t *v)
{
 return arch_atomic_add_return(-i, v);
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int arch_atomic_fetch_add(int i, atomic_t *v)
{
 return ({ __typeof__ (*(((&v->counter)))) __ret = (((i))); switch (sizeof(*(((&v->counter))))) { case 1: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "b %b0, %1\n" : "+q" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 2: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "w %w0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 4: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "l %0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 8: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "q %q0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; default: __xadd_wrong_size(); } __ret; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int arch_atomic_fetch_sub(int i, atomic_t *v)
{
 return ({ __typeof__ (*(((&v->counter)))) __ret = (((-i))); switch (sizeof(*(((&v->counter))))) { case 1: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "b %b0, %1\n" : "+q" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 2: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "w %w0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 4: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "l %0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 8: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "q %q0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; default: __xadd_wrong_size(); } __ret; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int arch_atomic_cmpxchg(atomic_t *v, int old, int new)
{
 return ({ __typeof__(*((&v->counter))) __ret; __typeof__(*((&v->counter))) __old = ((old)); __typeof__(*((&v->counter))) __new = ((new)); switch ((sizeof(*(&v->counter)))) { case 1: { volatile u8 *__ptr = (volatile u8 *)((&v->counter)); asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchgb %2,%1" : "=a" (__ret), "+m" (*__ptr) : "q" (__new), "0" (__old) : "memory"); break; } case 2: { volatile u16 *__ptr = (volatile u16 *)((&v->counter)); asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchgw %2,%1" : "=a" (__ret), "+m" (*__ptr) : "r" (__new), "0" (__old) : "memory"); break; } case 4: { volatile u32 *__ptr = (volatile u32 *)((&v->counter)); asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchgl %2,%1" : "=a" (__ret), "+m" (*__ptr) : "r" (__new), "0" (__old) : "memory"); break; } case 8: { volatile u64 *__ptr = (volatile u64 *)((&v->counter)); asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchgq %2,%1" : "=a" (__ret), "+m" (*__ptr) : "r" (__new), "0" (__old) : "memory"); break; } default: __cmpxchg_wrong_size(); } __ret; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool arch_atomic_try_cmpxchg(atomic_t *v, int *old, int new)
{
 return ({ bool success; __typeof__(((&v->counter))) _old = (__typeof__(((&v->counter))))(((old))); __typeof__(*(((&v->counter)))) __old = *_old; __typeof__(*(((&v->counter)))) __new = (((new))); switch ((sizeof(*(&v->counter)))) { case 1: { volatile u8 *__ptr = (volatile u8 *)(((&v->counter))); asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchgb %[new], %[ptr]" "\n\t/* output condition code " "z" "*/\n" : "=@cc" "z" (success), [ptr] "+m" (*__ptr), [old] "+a" (__old) : [new] "q" (__new) : "memory"); break; } case 2: { volatile u16 *__ptr = (volatile u16 *)(((&v->counter))); asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchgw %[new], %[ptr]" "\n\t/* output condition code " "z" "*/\n" : "=@cc" "z" (success), [ptr] "+m" (*__ptr), [old] "+a" (__old) : [new] "r" (__new) : "memory"); break; } case 4: { volatile u32 *__ptr = (volatile u32 *)(((&v->counter))); asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchgl %[new], %[ptr]" "\n\t/* output condition code " "z" "*/\n" : "=@cc" "z" (success), [ptr] "+m" (*__ptr), [old] "+a" (__old) : [new] "r" (__new) : "memory"); break; } case 8: { volatile u64 *__ptr = (volatile u64 *)(((&v->counter))); asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchgq %[new], %[ptr]" "\n\t/* output condition code " "z" "*/\n" : "=@cc" "z" (success), [ptr] "+m" (*__ptr), [old] "+a" (__old) : [new] "r" (__new) : "memory"); break; } default: __cmpxchg_wrong_size(); } if (__builtin_expect(!!(!success), 0)) *_old = __old; __builtin_expect(!!(success), 1); });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int arch_atomic_xchg(atomic_t *v, int new)
{
 return ({ __typeof__ (*((&v->counter))) __ret = ((new)); switch (sizeof(*((&v->counter)))) { case 1: asm volatile ("" "xchg" "b %b0, %1\n" : "+q" (__ret), "+m" (*((&v->counter))) : : "memory", "cc"); break; case 2: asm volatile ("" "xchg" "w %w0, %1\n" : "+r" (__ret), "+m" (*((&v->counter))) : : "memory", "cc"); break; case 4: asm volatile ("" "xchg" "l %0, %1\n" : "+r" (__ret), "+m" (*((&v->counter))) : : "memory", "cc"); break; case 8: asm volatile ("" "xchg" "q %q0, %1\n" : "+r" (__ret), "+m" (*((&v->counter))) : : "memory", "cc"); break; default: __xchg_wrong_size(); } __ret; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void arch_atomic_and(int i, atomic_t *v)
{
 asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "andl %1,%0"
   : "+m" (v->counter)
   : "ir" (i)
   : "memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int arch_atomic_fetch_and(int i, atomic_t *v)
{
 int val = arch_atomic_read(v);

 do { } while (!arch_atomic_try_cmpxchg(v, &val, val & i));

 return val;
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void arch_atomic_or(int i, atomic_t *v)
{
 asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "orl %1,%0"
   : "+m" (v->counter)
   : "ir" (i)
   : "memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int arch_atomic_fetch_or(int i, atomic_t *v)
{
 int val = arch_atomic_read(v);

 do { } while (!arch_atomic_try_cmpxchg(v, &val, val | i));

 return val;
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void arch_atomic_xor(int i, atomic_t *v)
{
 asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xorl %1,%0"
   : "+m" (v->counter)
   : "ir" (i)
   : "memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int arch_atomic_fetch_xor(int i, atomic_t *v)
{
 int val = arch_atomic_read(v);

 do { } while (!arch_atomic_try_cmpxchg(v, &val, val ^ i));

 return val;
}





# 1 "./arch/x86/include/asm/atomic64_64.h" 1
# 13 "./arch/x86/include/asm/atomic64_64.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64 arch_atomic64_read(const atomic64_t *v)
{
 return (*(const volatile typeof( _Generic(((v)->counter), char: (char)0, unsigned char: (unsigned char)0, signed char: (signed char)0, unsigned short: (unsigned short)0, signed short: (signed short)0, unsigned int: (unsigned int)0, signed int: (signed int)0, unsigned long: (unsigned long)0, signed long: (signed long)0, unsigned long long: (unsigned long long)0, signed long long: (signed long long)0, default: ((v)->counter))) *)&((v)->counter));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void arch_atomic64_set(atomic64_t *v, s64 i)
{
 do { *(volatile typeof(v->counter) *)&(v->counter) = (i); } while (0);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void arch_atomic64_add(s64 i, atomic64_t *v)
{
 asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "addq %1,%0"
       : "=m" (v->counter)
       : "er" (i), "m" (v->counter) : "memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void arch_atomic64_sub(s64 i, atomic64_t *v)
{
 asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "subq %1,%0"
       : "=m" (v->counter)
       : "er" (i), "m" (v->counter) : "memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool arch_atomic64_sub_and_test(s64 i, atomic64_t *v)
{
 return ({ bool c; asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "subq" " %[val], " "%[var]" "\n\t/* output condition code " "e" "*/\n" : [var] "+m" (v->counter), "=@cc" "e" (c) : [val] "er" (i) : "memory"); c; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void arch_atomic64_inc(atomic64_t *v)
{
 asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "incq %0"
       : "=m" (v->counter)
       : "m" (v->counter) : "memory");
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void arch_atomic64_dec(atomic64_t *v)
{
 asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "decq %0"
       : "=m" (v->counter)
       : "m" (v->counter) : "memory");
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool arch_atomic64_dec_and_test(atomic64_t *v)
{
 return ({ bool c; asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "decq" " " "%[var]" "\n\t/* output condition code " "e" "*/\n" : [var] "+m" (v->counter), "=@cc" "e" (c) : : "memory"); c; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool arch_atomic64_inc_and_test(atomic64_t *v)
{
 return ({ bool c; asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "incq" " " "%[var]" "\n\t/* output condition code " "e" "*/\n" : [var] "+m" (v->counter), "=@cc" "e" (c) : : "memory"); c; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool arch_atomic64_add_negative(s64 i, atomic64_t *v)
{
 return ({ bool c; asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "addq" " %[val], " "%[var]" "\n\t/* output condition code " "s" "*/\n" : [var] "+m" (v->counter), "=@cc" "s" (c) : [val] "er" (i) : "memory"); c; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64 arch_atomic64_add_return(s64 i, atomic64_t *v)
{
 return i + ({ __typeof__ (*(((&v->counter)))) __ret = (((i))); switch (sizeof(*(((&v->counter))))) { case 1: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "b %b0, %1\n" : "+q" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 2: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "w %w0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 4: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "l %0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 8: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "q %q0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; default: __xadd_wrong_size(); } __ret; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64 arch_atomic64_sub_return(s64 i, atomic64_t *v)
{
 return arch_atomic64_add_return(-i, v);
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64 arch_atomic64_fetch_add(s64 i, atomic64_t *v)
{
 return ({ __typeof__ (*(((&v->counter)))) __ret = (((i))); switch (sizeof(*(((&v->counter))))) { case 1: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "b %b0, %1\n" : "+q" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 2: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "w %w0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 4: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "l %0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 8: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "q %q0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; default: __xadd_wrong_size(); } __ret; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64 arch_atomic64_fetch_sub(s64 i, atomic64_t *v)
{
 return ({ __typeof__ (*(((&v->counter)))) __ret = (((-i))); switch (sizeof(*(((&v->counter))))) { case 1: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "b %b0, %1\n" : "+q" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 2: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "w %w0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 4: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "l %0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; case 8: asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xadd" "q %q0, %1\n" : "+r" (__ret), "+m" (*(((&v->counter)))) : : "memory", "cc"); break; default: __xadd_wrong_size(); } __ret; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64 arch_atomic64_cmpxchg(atomic64_t *v, s64 old, s64 new)
{
 return ({ __typeof__(*((&v->counter))) __ret; __typeof__(*((&v->counter))) __old = ((old)); __typeof__(*((&v->counter))) __new = ((new)); switch ((sizeof(*(&v->counter)))) { case 1: { volatile u8 *__ptr = (volatile u8 *)((&v->counter)); asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchgb %2,%1" : "=a" (__ret), "+m" (*__ptr) : "q" (__new), "0" (__old) : "memory"); break; } case 2: { volatile u16 *__ptr = (volatile u16 *)((&v->counter)); asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchgw %2,%1" : "=a" (__ret), "+m" (*__ptr) : "r" (__new), "0" (__old) : "memory"); break; } case 4: { volatile u32 *__ptr = (volatile u32 *)((&v->counter)); asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchgl %2,%1" : "=a" (__ret), "+m" (*__ptr) : "r" (__new), "0" (__old) : "memory"); break; } case 8: { volatile u64 *__ptr = (volatile u64 *)((&v->counter)); asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchgq %2,%1" : "=a" (__ret), "+m" (*__ptr) : "r" (__new), "0" (__old) : "memory"); break; } default: __cmpxchg_wrong_size(); } __ret; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool arch_atomic64_try_cmpxchg(atomic64_t *v, s64 *old, s64 new)
{
 return ({ bool success; __typeof__(((&v->counter))) _old = (__typeof__(((&v->counter))))(((old))); __typeof__(*(((&v->counter)))) __old = *_old; __typeof__(*(((&v->counter)))) __new = (((new))); switch ((sizeof(*(&v->counter)))) { case 1: { volatile u8 *__ptr = (volatile u8 *)(((&v->counter))); asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchgb %[new], %[ptr]" "\n\t/* output condition code " "z" "*/\n" : "=@cc" "z" (success), [ptr] "+m" (*__ptr), [old] "+a" (__old) : [new] "q" (__new) : "memory"); break; } case 2: { volatile u16 *__ptr = (volatile u16 *)(((&v->counter))); asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchgw %[new], %[ptr]" "\n\t/* output condition code " "z" "*/\n" : "=@cc" "z" (success), [ptr] "+m" (*__ptr), [old] "+a" (__old) : [new] "r" (__new) : "memory"); break; } case 4: { volatile u32 *__ptr = (volatile u32 *)(((&v->counter))); asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchgl %[new], %[ptr]" "\n\t/* output condition code " "z" "*/\n" : "=@cc" "z" (success), [ptr] "+m" (*__ptr), [old] "+a" (__old) : [new] "r" (__new) : "memory"); break; } case 8: { volatile u64 *__ptr = (volatile u64 *)(((&v->counter))); asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "cmpxchgq %[new], %[ptr]" "\n\t/* output condition code " "z" "*/\n" : "=@cc" "z" (success), [ptr] "+m" (*__ptr), [old] "+a" (__old) : [new] "r" (__new) : "memory"); break; } default: __cmpxchg_wrong_size(); } if (__builtin_expect(!!(!success), 0)) *_old = __old; __builtin_expect(!!(success), 1); });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64 arch_atomic64_xchg(atomic64_t *v, s64 new)
{
 return ({ __typeof__ (*((&v->counter))) __ret = ((new)); switch (sizeof(*((&v->counter)))) { case 1: asm volatile ("" "xchg" "b %b0, %1\n" : "+q" (__ret), "+m" (*((&v->counter))) : : "memory", "cc"); break; case 2: asm volatile ("" "xchg" "w %w0, %1\n" : "+r" (__ret), "+m" (*((&v->counter))) : : "memory", "cc"); break; case 4: asm volatile ("" "xchg" "l %0, %1\n" : "+r" (__ret), "+m" (*((&v->counter))) : : "memory", "cc"); break; case 8: asm volatile ("" "xchg" "q %q0, %1\n" : "+r" (__ret), "+m" (*((&v->counter))) : : "memory", "cc"); break; default: __xchg_wrong_size(); } __ret; });
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void arch_atomic64_and(s64 i, atomic64_t *v)
{
 asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "andq %1,%0"
   : "+m" (v->counter)
   : "er" (i)
   : "memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64 arch_atomic64_fetch_and(s64 i, atomic64_t *v)
{
 s64 val = arch_atomic64_read(v);

 do {
 } while (!arch_atomic64_try_cmpxchg(v, &val, val & i));
 return val;
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void arch_atomic64_or(s64 i, atomic64_t *v)
{
 asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "orq %1,%0"
   : "+m" (v->counter)
   : "er" (i)
   : "memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64 arch_atomic64_fetch_or(s64 i, atomic64_t *v)
{
 s64 val = arch_atomic64_read(v);

 do {
 } while (!arch_atomic64_try_cmpxchg(v, &val, val | i));
 return val;
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void arch_atomic64_xor(s64 i, atomic64_t *v)
{
 asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xorq %1,%0"
   : "+m" (v->counter)
   : "er" (i)
   : "memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64 arch_atomic64_fetch_xor(s64 i, atomic64_t *v)
{
 s64 val = arch_atomic64_read(v);

 do {
 } while (!arch_atomic64_try_cmpxchg(v, &val, val ^ i));
 return val;
}
# 183 "./arch/x86/include/asm/atomic.h" 2
# 8 "./include/linux/atomic.h" 2
# 80 "./include/linux/atomic.h"
# 1 "./include/linux/atomic/atomic-arch-fallback.h" 1
# 454 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_read(const atomic_t *v)
{
 return arch_atomic_read(v);
}
# 470 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_read_acquire(const atomic_t *v)
{



 int ret;

 if ((sizeof(atomic_t) == sizeof(char) || sizeof(atomic_t) == sizeof(short) || sizeof(atomic_t) == sizeof(int) || sizeof(atomic_t) == sizeof(long))) {
  ret = ({ typeof(*&(v)->counter) ___p1 = ({ do { __attribute__((__noreturn__)) extern void __compiletime_assert_0(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(*&(v)->counter) == sizeof(char) || sizeof(*&(v)->counter) == sizeof(short) || sizeof(*&(v)->counter) == sizeof(int) || sizeof(*&(v)->counter) == sizeof(long)) || sizeof(*&(v)->counter) == sizeof(long long))) __compiletime_assert_0(); } while (0); (*(const volatile typeof( _Generic((*&(v)->counter), char: (char)0, unsigned char: (unsigned char)0, signed char: (signed char)0, unsigned short: (unsigned short)0, signed short: (signed short)0, unsigned int: (unsigned int)0, signed int: (signed int)0, unsigned long: (unsigned long)0, signed long: (signed long)0, unsigned long long: (unsigned long long)0, signed long long: (signed long long)0, default: (*&(v)->counter))) *)&(*&(v)->counter)); }); do { __attribute__((__noreturn__)) extern void __compiletime_assert_1(void) __attribute__((__error__("Need native word sized stores/loads for atomicity."))); if (!((sizeof(*&(v)->counter) == sizeof(char) || sizeof(*&(v)->counter) == sizeof(short) || sizeof(*&(v)->counter) == sizeof(int) || sizeof(*&(v)->counter) == sizeof(long)))) __compiletime_assert_1(); } while (0); __asm__ __volatile__("": : :"memory"); ___p1; });
 } else {
  ret = raw_atomic_read(v);
  do { do { } while (0); do { } while (0); } while (0);
 }

 return ret;

}
# 500 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_set(atomic_t *v, int i)
{
 arch_atomic_set(v, i);
}
# 517 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_set_release(atomic_t *v, int i)
{



 if ((sizeof(atomic_t) == sizeof(char) || sizeof(atomic_t) == sizeof(short) || sizeof(atomic_t) == sizeof(int) || sizeof(atomic_t) == sizeof(long))) {
  do { do { } while (0); do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_2(void) __attribute__((__error__("Need native word sized stores/loads for atomicity."))); if (!((sizeof(*&(v)->counter) == sizeof(char) || sizeof(*&(v)->counter) == sizeof(short) || sizeof(*&(v)->counter) == sizeof(int) || sizeof(*&(v)->counter) == sizeof(long)))) __compiletime_assert_2(); } while (0); __asm__ __volatile__("": : :"memory"); do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_3(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(*&(v)->counter) == sizeof(char) || sizeof(*&(v)->counter) == sizeof(short) || sizeof(*&(v)->counter) == sizeof(int) || sizeof(*&(v)->counter) == sizeof(long)) || sizeof(*&(v)->counter) == sizeof(long long))) __compiletime_assert_3(); } while (0); do { *(volatile typeof(*&(v)->counter) *)&(*&(v)->counter) = (i); } while (0); } while (0); } while (0); } while (0);
 } else {
  do { do { } while (0); do { } while (0); } while (0);
  raw_atomic_set(v, i);
 }

}
# 543 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_add(int i, atomic_t *v)
{
 arch_atomic_add(i, v);
}
# 560 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_add_return(int i, atomic_t *v)
{

 return arch_atomic_add_return(i, v);
# 574 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 587 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_add_return_acquire(int i, atomic_t *v)
{







 return arch_atomic_add_return(i, v);



}
# 614 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_add_return_release(int i, atomic_t *v)
{






 return arch_atomic_add_return(i, v);



}
# 640 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_add_return_relaxed(int i, atomic_t *v)
{



 return arch_atomic_add_return(i, v);



}
# 663 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_add(int i, atomic_t *v)
{

 return arch_atomic_fetch_add(i, v);
# 677 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 690 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_add_acquire(int i, atomic_t *v)
{







 return arch_atomic_fetch_add(i, v);



}
# 717 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_add_release(int i, atomic_t *v)
{






 return arch_atomic_fetch_add(i, v);



}
# 743 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_add_relaxed(int i, atomic_t *v)
{



 return arch_atomic_fetch_add(i, v);



}
# 766 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_sub(int i, atomic_t *v)
{
 arch_atomic_sub(i, v);
}
# 783 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_sub_return(int i, atomic_t *v)
{

 return arch_atomic_sub_return(i, v);
# 797 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 810 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_sub_return_acquire(int i, atomic_t *v)
{







 return arch_atomic_sub_return(i, v);



}
# 837 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_sub_return_release(int i, atomic_t *v)
{






 return arch_atomic_sub_return(i, v);



}
# 863 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_sub_return_relaxed(int i, atomic_t *v)
{



 return arch_atomic_sub_return(i, v);



}
# 886 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_sub(int i, atomic_t *v)
{

 return arch_atomic_fetch_sub(i, v);
# 900 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 913 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_sub_acquire(int i, atomic_t *v)
{







 return arch_atomic_fetch_sub(i, v);



}
# 940 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_sub_release(int i, atomic_t *v)
{






 return arch_atomic_fetch_sub(i, v);



}
# 966 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_sub_relaxed(int i, atomic_t *v)
{



 return arch_atomic_fetch_sub(i, v);



}
# 988 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_inc(atomic_t *v)
{

 arch_atomic_inc(v);



}
# 1008 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_inc_return(atomic_t *v)
{
# 1020 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic_add_return(1, v);

}
# 1034 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_inc_return_acquire(atomic_t *v)
{
# 1046 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic_add_return_acquire(1, v);

}
# 1060 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_inc_return_release(atomic_t *v)
{
# 1071 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic_add_return_release(1, v);

}
# 1085 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_inc_return_relaxed(atomic_t *v)
{





 return raw_atomic_add_return_relaxed(1, v);

}
# 1107 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_inc(atomic_t *v)
{
# 1119 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic_fetch_add(1, v);

}
# 1133 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_inc_acquire(atomic_t *v)
{
# 1145 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic_fetch_add_acquire(1, v);

}
# 1159 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_inc_release(atomic_t *v)
{
# 1170 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic_fetch_add_release(1, v);

}
# 1184 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_inc_relaxed(atomic_t *v)
{





 return raw_atomic_fetch_add_relaxed(1, v);

}
# 1206 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_dec(atomic_t *v)
{

 arch_atomic_dec(v);



}
# 1226 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_dec_return(atomic_t *v)
{
# 1238 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic_sub_return(1, v);

}
# 1252 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_dec_return_acquire(atomic_t *v)
{
# 1264 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic_sub_return_acquire(1, v);

}
# 1278 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_dec_return_release(atomic_t *v)
{
# 1289 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic_sub_return_release(1, v);

}
# 1303 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_dec_return_relaxed(atomic_t *v)
{





 return raw_atomic_sub_return_relaxed(1, v);

}
# 1325 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_dec(atomic_t *v)
{
# 1337 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic_fetch_sub(1, v);

}
# 1351 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_dec_acquire(atomic_t *v)
{
# 1363 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic_fetch_sub_acquire(1, v);

}
# 1377 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_dec_release(atomic_t *v)
{
# 1388 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic_fetch_sub_release(1, v);

}
# 1402 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_dec_relaxed(atomic_t *v)
{





 return raw_atomic_fetch_sub_relaxed(1, v);

}
# 1425 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_and(int i, atomic_t *v)
{
 arch_atomic_and(i, v);
}
# 1442 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_and(int i, atomic_t *v)
{

 return arch_atomic_fetch_and(i, v);
# 1456 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 1469 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_and_acquire(int i, atomic_t *v)
{







 return arch_atomic_fetch_and(i, v);



}
# 1496 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_and_release(int i, atomic_t *v)
{






 return arch_atomic_fetch_and(i, v);



}
# 1522 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_and_relaxed(int i, atomic_t *v)
{



 return arch_atomic_fetch_and(i, v);



}
# 1545 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_andnot(int i, atomic_t *v)
{



 raw_atomic_and(~i, v);

}
# 1566 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_andnot(int i, atomic_t *v)
{
# 1578 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic_fetch_and(~i, v);

}
# 1593 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_andnot_acquire(int i, atomic_t *v)
{
# 1605 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic_fetch_and_acquire(~i, v);

}
# 1620 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_andnot_release(int i, atomic_t *v)
{
# 1631 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic_fetch_and_release(~i, v);

}
# 1646 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_andnot_relaxed(int i, atomic_t *v)
{





 return raw_atomic_fetch_and_relaxed(~i, v);

}
# 1669 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_or(int i, atomic_t *v)
{
 arch_atomic_or(i, v);
}
# 1686 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_or(int i, atomic_t *v)
{

 return arch_atomic_fetch_or(i, v);
# 1700 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 1713 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_or_acquire(int i, atomic_t *v)
{







 return arch_atomic_fetch_or(i, v);



}
# 1740 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_or_release(int i, atomic_t *v)
{






 return arch_atomic_fetch_or(i, v);



}
# 1766 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_or_relaxed(int i, atomic_t *v)
{



 return arch_atomic_fetch_or(i, v);



}
# 1789 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_xor(int i, atomic_t *v)
{
 arch_atomic_xor(i, v);
}
# 1806 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_xor(int i, atomic_t *v)
{

 return arch_atomic_fetch_xor(i, v);
# 1820 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 1833 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_xor_acquire(int i, atomic_t *v)
{







 return arch_atomic_fetch_xor(i, v);



}
# 1860 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_xor_release(int i, atomic_t *v)
{






 return arch_atomic_fetch_xor(i, v);



}
# 1886 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_xor_relaxed(int i, atomic_t *v)
{



 return arch_atomic_fetch_xor(i, v);



}
# 1909 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_xchg(atomic_t *v, int new)
{

 return arch_atomic_xchg(v, new);
# 1923 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 1936 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_xchg_acquire(atomic_t *v, int new)
{







 return arch_atomic_xchg(v, new);



}
# 1963 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_xchg_release(atomic_t *v, int new)
{






 return arch_atomic_xchg(v, new);



}
# 1989 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_xchg_relaxed(atomic_t *v, int new)
{



 return arch_atomic_xchg(v, new);



}
# 2013 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_cmpxchg(atomic_t *v, int old, int new)
{

 return arch_atomic_cmpxchg(v, old, new);
# 2027 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 2041 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_cmpxchg_acquire(atomic_t *v, int old, int new)
{







 return arch_atomic_cmpxchg(v, old, new);



}
# 2069 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_cmpxchg_release(atomic_t *v, int old, int new)
{






 return arch_atomic_cmpxchg(v, old, new);



}
# 2096 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_cmpxchg_relaxed(atomic_t *v, int old, int new)
{



 return arch_atomic_cmpxchg(v, old, new);



}
# 2121 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_try_cmpxchg(atomic_t *v, int *old, int new)
{

 return arch_atomic_try_cmpxchg(v, old, new);
# 2139 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 2154 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_try_cmpxchg_acquire(atomic_t *v, int *old, int new)
{







 return arch_atomic_try_cmpxchg(v, old, new);







}
# 2187 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_try_cmpxchg_release(atomic_t *v, int *old, int new)
{






 return arch_atomic_try_cmpxchg(v, old, new);







}
# 2219 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_try_cmpxchg_relaxed(atomic_t *v, int *old, int new)
{



 return arch_atomic_try_cmpxchg(v, old, new);







}
# 2246 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_sub_and_test(int i, atomic_t *v)
{

 return arch_atomic_sub_and_test(i, v);



}
# 2266 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_dec_and_test(atomic_t *v)
{

 return arch_atomic_dec_and_test(v);



}
# 2286 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_inc_and_test(atomic_t *v)
{

 return arch_atomic_inc_and_test(v);



}
# 2307 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_add_negative(int i, atomic_t *v)
{

 return arch_atomic_add_negative(i, v);
# 2321 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 2334 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_add_negative_acquire(int i, atomic_t *v)
{







 return arch_atomic_add_negative(i, v);



}
# 2361 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_add_negative_release(int i, atomic_t *v)
{






 return arch_atomic_add_negative(i, v);



}
# 2387 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_add_negative_relaxed(int i, atomic_t *v)
{



 return arch_atomic_add_negative(i, v);



}
# 2411 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_fetch_add_unless(atomic_t *v, int a, int u)
{



 int c = raw_atomic_read(v);

 do {
  if (__builtin_expect(!!(c == u), 0))
   break;
 } while (!raw_atomic_try_cmpxchg(v, &c, c + a));

 return c;

}
# 2440 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_add_unless(atomic_t *v, int a, int u)
{



 return raw_atomic_fetch_add_unless(v, a, u) != u;

}
# 2460 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_inc_not_zero(atomic_t *v)
{



 return raw_atomic_add_unless(v, 1, 0);

}
# 2480 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_inc_unless_negative(atomic_t *v)
{



 int c = raw_atomic_read(v);

 do {
  if (__builtin_expect(!!(c < 0), 0))
   return false;
 } while (!raw_atomic_try_cmpxchg(v, &c, c + 1));

 return true;

}
# 2507 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_dec_unless_positive(atomic_t *v)
{



 int c = raw_atomic_read(v);

 do {
  if (__builtin_expect(!!(c > 0), 0))
   return false;
 } while (!raw_atomic_try_cmpxchg(v, &c, c - 1));

 return true;

}
# 2534 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
raw_atomic_dec_if_positive(atomic_t *v)
{



 int dec, c = raw_atomic_read(v);

 do {
  dec = c - 1;
  if (__builtin_expect(!!(dec < 0), 0))
   break;
 } while (!raw_atomic_try_cmpxchg(v, &c, dec));

 return dec;

}
# 2566 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_read(const atomic64_t *v)
{
 return arch_atomic64_read(v);
}
# 2582 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_read_acquire(const atomic64_t *v)
{



 s64 ret;

 if ((sizeof(atomic64_t) == sizeof(char) || sizeof(atomic64_t) == sizeof(short) || sizeof(atomic64_t) == sizeof(int) || sizeof(atomic64_t) == sizeof(long))) {
  ret = ({ typeof(*&(v)->counter) ___p1 = ({ do { __attribute__((__noreturn__)) extern void __compiletime_assert_4(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(*&(v)->counter) == sizeof(char) || sizeof(*&(v)->counter) == sizeof(short) || sizeof(*&(v)->counter) == sizeof(int) || sizeof(*&(v)->counter) == sizeof(long)) || sizeof(*&(v)->counter) == sizeof(long long))) __compiletime_assert_4(); } while (0); (*(const volatile typeof( _Generic((*&(v)->counter), char: (char)0, unsigned char: (unsigned char)0, signed char: (signed char)0, unsigned short: (unsigned short)0, signed short: (signed short)0, unsigned int: (unsigned int)0, signed int: (signed int)0, unsigned long: (unsigned long)0, signed long: (signed long)0, unsigned long long: (unsigned long long)0, signed long long: (signed long long)0, default: (*&(v)->counter))) *)&(*&(v)->counter)); }); do { __attribute__((__noreturn__)) extern void __compiletime_assert_5(void) __attribute__((__error__("Need native word sized stores/loads for atomicity."))); if (!((sizeof(*&(v)->counter) == sizeof(char) || sizeof(*&(v)->counter) == sizeof(short) || sizeof(*&(v)->counter) == sizeof(int) || sizeof(*&(v)->counter) == sizeof(long)))) __compiletime_assert_5(); } while (0); __asm__ __volatile__("": : :"memory"); ___p1; });
 } else {
  ret = raw_atomic64_read(v);
  do { do { } while (0); do { } while (0); } while (0);
 }

 return ret;

}
# 2612 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic64_set(atomic64_t *v, s64 i)
{
 arch_atomic64_set(v, i);
}
# 2629 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic64_set_release(atomic64_t *v, s64 i)
{



 if ((sizeof(atomic64_t) == sizeof(char) || sizeof(atomic64_t) == sizeof(short) || sizeof(atomic64_t) == sizeof(int) || sizeof(atomic64_t) == sizeof(long))) {
  do { do { } while (0); do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_6(void) __attribute__((__error__("Need native word sized stores/loads for atomicity."))); if (!((sizeof(*&(v)->counter) == sizeof(char) || sizeof(*&(v)->counter) == sizeof(short) || sizeof(*&(v)->counter) == sizeof(int) || sizeof(*&(v)->counter) == sizeof(long)))) __compiletime_assert_6(); } while (0); __asm__ __volatile__("": : :"memory"); do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_7(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(*&(v)->counter) == sizeof(char) || sizeof(*&(v)->counter) == sizeof(short) || sizeof(*&(v)->counter) == sizeof(int) || sizeof(*&(v)->counter) == sizeof(long)) || sizeof(*&(v)->counter) == sizeof(long long))) __compiletime_assert_7(); } while (0); do { *(volatile typeof(*&(v)->counter) *)&(*&(v)->counter) = (i); } while (0); } while (0); } while (0); } while (0);
 } else {
  do { do { } while (0); do { } while (0); } while (0);
  raw_atomic64_set(v, i);
 }

}
# 2655 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic64_add(s64 i, atomic64_t *v)
{
 arch_atomic64_add(i, v);
}
# 2672 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_add_return(s64 i, atomic64_t *v)
{

 return arch_atomic64_add_return(i, v);
# 2686 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 2699 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_add_return_acquire(s64 i, atomic64_t *v)
{







 return arch_atomic64_add_return(i, v);



}
# 2726 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_add_return_release(s64 i, atomic64_t *v)
{






 return arch_atomic64_add_return(i, v);



}
# 2752 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_add_return_relaxed(s64 i, atomic64_t *v)
{



 return arch_atomic64_add_return(i, v);



}
# 2775 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_add(s64 i, atomic64_t *v)
{

 return arch_atomic64_fetch_add(i, v);
# 2789 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 2802 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_add_acquire(s64 i, atomic64_t *v)
{







 return arch_atomic64_fetch_add(i, v);



}
# 2829 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_add_release(s64 i, atomic64_t *v)
{






 return arch_atomic64_fetch_add(i, v);



}
# 2855 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_add_relaxed(s64 i, atomic64_t *v)
{



 return arch_atomic64_fetch_add(i, v);



}
# 2878 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic64_sub(s64 i, atomic64_t *v)
{
 arch_atomic64_sub(i, v);
}
# 2895 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_sub_return(s64 i, atomic64_t *v)
{

 return arch_atomic64_sub_return(i, v);
# 2909 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 2922 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_sub_return_acquire(s64 i, atomic64_t *v)
{







 return arch_atomic64_sub_return(i, v);



}
# 2949 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_sub_return_release(s64 i, atomic64_t *v)
{






 return arch_atomic64_sub_return(i, v);



}
# 2975 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_sub_return_relaxed(s64 i, atomic64_t *v)
{



 return arch_atomic64_sub_return(i, v);



}
# 2998 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_sub(s64 i, atomic64_t *v)
{

 return arch_atomic64_fetch_sub(i, v);
# 3012 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 3025 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_sub_acquire(s64 i, atomic64_t *v)
{







 return arch_atomic64_fetch_sub(i, v);



}
# 3052 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_sub_release(s64 i, atomic64_t *v)
{






 return arch_atomic64_fetch_sub(i, v);



}
# 3078 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_sub_relaxed(s64 i, atomic64_t *v)
{



 return arch_atomic64_fetch_sub(i, v);



}
# 3100 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic64_inc(atomic64_t *v)
{

 arch_atomic64_inc(v);



}
# 3120 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_inc_return(atomic64_t *v)
{
# 3132 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic64_add_return(1, v);

}
# 3146 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_inc_return_acquire(atomic64_t *v)
{
# 3158 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic64_add_return_acquire(1, v);

}
# 3172 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_inc_return_release(atomic64_t *v)
{
# 3183 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic64_add_return_release(1, v);

}
# 3197 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_inc_return_relaxed(atomic64_t *v)
{





 return raw_atomic64_add_return_relaxed(1, v);

}
# 3219 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_inc(atomic64_t *v)
{
# 3231 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic64_fetch_add(1, v);

}
# 3245 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_inc_acquire(atomic64_t *v)
{
# 3257 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic64_fetch_add_acquire(1, v);

}
# 3271 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_inc_release(atomic64_t *v)
{
# 3282 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic64_fetch_add_release(1, v);

}
# 3296 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_inc_relaxed(atomic64_t *v)
{





 return raw_atomic64_fetch_add_relaxed(1, v);

}
# 3318 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic64_dec(atomic64_t *v)
{

 arch_atomic64_dec(v);



}
# 3338 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_dec_return(atomic64_t *v)
{
# 3350 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic64_sub_return(1, v);

}
# 3364 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_dec_return_acquire(atomic64_t *v)
{
# 3376 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic64_sub_return_acquire(1, v);

}
# 3390 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_dec_return_release(atomic64_t *v)
{
# 3401 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic64_sub_return_release(1, v);

}
# 3415 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_dec_return_relaxed(atomic64_t *v)
{





 return raw_atomic64_sub_return_relaxed(1, v);

}
# 3437 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_dec(atomic64_t *v)
{
# 3449 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic64_fetch_sub(1, v);

}
# 3463 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_dec_acquire(atomic64_t *v)
{
# 3475 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic64_fetch_sub_acquire(1, v);

}
# 3489 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_dec_release(atomic64_t *v)
{
# 3500 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic64_fetch_sub_release(1, v);

}
# 3514 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_dec_relaxed(atomic64_t *v)
{





 return raw_atomic64_fetch_sub_relaxed(1, v);

}
# 3537 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic64_and(s64 i, atomic64_t *v)
{
 arch_atomic64_and(i, v);
}
# 3554 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_and(s64 i, atomic64_t *v)
{

 return arch_atomic64_fetch_and(i, v);
# 3568 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 3581 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_and_acquire(s64 i, atomic64_t *v)
{







 return arch_atomic64_fetch_and(i, v);



}
# 3608 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_and_release(s64 i, atomic64_t *v)
{






 return arch_atomic64_fetch_and(i, v);



}
# 3634 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_and_relaxed(s64 i, atomic64_t *v)
{



 return arch_atomic64_fetch_and(i, v);



}
# 3657 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic64_andnot(s64 i, atomic64_t *v)
{



 raw_atomic64_and(~i, v);

}
# 3678 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_andnot(s64 i, atomic64_t *v)
{
# 3690 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic64_fetch_and(~i, v);

}
# 3705 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_andnot_acquire(s64 i, atomic64_t *v)
{
# 3717 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic64_fetch_and_acquire(~i, v);

}
# 3732 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_andnot_release(s64 i, atomic64_t *v)
{
# 3743 "./include/linux/atomic/atomic-arch-fallback.h"
 return raw_atomic64_fetch_and_release(~i, v);

}
# 3758 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_andnot_relaxed(s64 i, atomic64_t *v)
{





 return raw_atomic64_fetch_and_relaxed(~i, v);

}
# 3781 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic64_or(s64 i, atomic64_t *v)
{
 arch_atomic64_or(i, v);
}
# 3798 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_or(s64 i, atomic64_t *v)
{

 return arch_atomic64_fetch_or(i, v);
# 3812 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 3825 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_or_acquire(s64 i, atomic64_t *v)
{







 return arch_atomic64_fetch_or(i, v);



}
# 3852 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_or_release(s64 i, atomic64_t *v)
{






 return arch_atomic64_fetch_or(i, v);



}
# 3878 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_or_relaxed(s64 i, atomic64_t *v)
{



 return arch_atomic64_fetch_or(i, v);



}
# 3901 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic64_xor(s64 i, atomic64_t *v)
{
 arch_atomic64_xor(i, v);
}
# 3918 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_xor(s64 i, atomic64_t *v)
{

 return arch_atomic64_fetch_xor(i, v);
# 3932 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 3945 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_xor_acquire(s64 i, atomic64_t *v)
{







 return arch_atomic64_fetch_xor(i, v);



}
# 3972 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_xor_release(s64 i, atomic64_t *v)
{






 return arch_atomic64_fetch_xor(i, v);



}
# 3998 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_xor_relaxed(s64 i, atomic64_t *v)
{



 return arch_atomic64_fetch_xor(i, v);



}
# 4021 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_xchg(atomic64_t *v, s64 new)
{

 return arch_atomic64_xchg(v, new);
# 4035 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 4048 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_xchg_acquire(atomic64_t *v, s64 new)
{







 return arch_atomic64_xchg(v, new);



}
# 4075 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_xchg_release(atomic64_t *v, s64 new)
{






 return arch_atomic64_xchg(v, new);



}
# 4101 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_xchg_relaxed(atomic64_t *v, s64 new)
{



 return arch_atomic64_xchg(v, new);



}
# 4125 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_cmpxchg(atomic64_t *v, s64 old, s64 new)
{

 return arch_atomic64_cmpxchg(v, old, new);
# 4139 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 4153 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_cmpxchg_acquire(atomic64_t *v, s64 old, s64 new)
{







 return arch_atomic64_cmpxchg(v, old, new);



}
# 4181 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_cmpxchg_release(atomic64_t *v, s64 old, s64 new)
{






 return arch_atomic64_cmpxchg(v, old, new);



}
# 4208 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_cmpxchg_relaxed(atomic64_t *v, s64 old, s64 new)
{



 return arch_atomic64_cmpxchg(v, old, new);



}
# 4233 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic64_try_cmpxchg(atomic64_t *v, s64 *old, s64 new)
{

 return arch_atomic64_try_cmpxchg(v, old, new);
# 4251 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 4266 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic64_try_cmpxchg_acquire(atomic64_t *v, s64 *old, s64 new)
{







 return arch_atomic64_try_cmpxchg(v, old, new);







}
# 4299 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic64_try_cmpxchg_release(atomic64_t *v, s64 *old, s64 new)
{






 return arch_atomic64_try_cmpxchg(v, old, new);







}
# 4331 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic64_try_cmpxchg_relaxed(atomic64_t *v, s64 *old, s64 new)
{



 return arch_atomic64_try_cmpxchg(v, old, new);







}
# 4358 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic64_sub_and_test(s64 i, atomic64_t *v)
{

 return arch_atomic64_sub_and_test(i, v);



}
# 4378 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic64_dec_and_test(atomic64_t *v)
{

 return arch_atomic64_dec_and_test(v);



}
# 4398 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic64_inc_and_test(atomic64_t *v)
{

 return arch_atomic64_inc_and_test(v);



}
# 4419 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic64_add_negative(s64 i, atomic64_t *v)
{

 return arch_atomic64_add_negative(i, v);
# 4433 "./include/linux/atomic/atomic-arch-fallback.h"
}
# 4446 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic64_add_negative_acquire(s64 i, atomic64_t *v)
{







 return arch_atomic64_add_negative(i, v);



}
# 4473 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic64_add_negative_release(s64 i, atomic64_t *v)
{






 return arch_atomic64_add_negative(i, v);



}
# 4499 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic64_add_negative_relaxed(s64 i, atomic64_t *v)
{



 return arch_atomic64_add_negative(i, v);



}
# 4523 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_fetch_add_unless(atomic64_t *v, s64 a, s64 u)
{



 s64 c = raw_atomic64_read(v);

 do {
  if (__builtin_expect(!!(c == u), 0))
   break;
 } while (!raw_atomic64_try_cmpxchg(v, &c, c + a));

 return c;

}
# 4552 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic64_add_unless(atomic64_t *v, s64 a, s64 u)
{



 return raw_atomic64_fetch_add_unless(v, a, u) != u;

}
# 4572 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic64_inc_not_zero(atomic64_t *v)
{



 return raw_atomic64_add_unless(v, 1, 0);

}
# 4592 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic64_inc_unless_negative(atomic64_t *v)
{



 s64 c = raw_atomic64_read(v);

 do {
  if (__builtin_expect(!!(c < 0), 0))
   return false;
 } while (!raw_atomic64_try_cmpxchg(v, &c, c + 1));

 return true;

}
# 4619 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic64_dec_unless_positive(atomic64_t *v)
{



 s64 c = raw_atomic64_read(v);

 do {
  if (__builtin_expect(!!(c > 0), 0))
   return false;
 } while (!raw_atomic64_try_cmpxchg(v, &c, c - 1));

 return true;

}
# 4646 "./include/linux/atomic/atomic-arch-fallback.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
raw_atomic64_dec_if_positive(atomic64_t *v)
{



 s64 dec, c = raw_atomic64_read(v);

 do {
  dec = c - 1;
  if (__builtin_expect(!!(dec < 0), 0))
   break;
 } while (!raw_atomic64_try_cmpxchg(v, &c, dec));

 return dec;

}
# 81 "./include/linux/atomic.h" 2
# 1 "./include/linux/atomic/atomic-long.h" 1
# 10 "./include/linux/atomic/atomic-long.h"
# 1 "./arch/x86/include/generated/uapi/asm/types.h" 1
# 11 "./include/linux/atomic/atomic-long.h" 2


typedef atomic64_t atomic_long_t;
# 34 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_read(const atomic_long_t *v)
{

 return raw_atomic64_read(v);



}
# 54 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_read_acquire(const atomic_long_t *v)
{

 return raw_atomic64_read_acquire(v);



}
# 75 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_long_set(atomic_long_t *v, long i)
{

 raw_atomic64_set(v, i);



}
# 96 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_long_set_release(atomic_long_t *v, long i)
{

 raw_atomic64_set_release(v, i);



}
# 117 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_long_add(long i, atomic_long_t *v)
{

 raw_atomic64_add(i, v);



}
# 138 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_add_return(long i, atomic_long_t *v)
{

 return raw_atomic64_add_return(i, v);



}
# 159 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_add_return_acquire(long i, atomic_long_t *v)
{

 return raw_atomic64_add_return_acquire(i, v);



}
# 180 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_add_return_release(long i, atomic_long_t *v)
{

 return raw_atomic64_add_return_release(i, v);



}
# 201 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_add_return_relaxed(long i, atomic_long_t *v)
{

 return raw_atomic64_add_return_relaxed(i, v);



}
# 222 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_add(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_add(i, v);



}
# 243 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_add_acquire(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_add_acquire(i, v);



}
# 264 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_add_release(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_add_release(i, v);



}
# 285 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_add_relaxed(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_add_relaxed(i, v);



}
# 306 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_long_sub(long i, atomic_long_t *v)
{

 raw_atomic64_sub(i, v);



}
# 327 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_sub_return(long i, atomic_long_t *v)
{

 return raw_atomic64_sub_return(i, v);



}
# 348 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_sub_return_acquire(long i, atomic_long_t *v)
{

 return raw_atomic64_sub_return_acquire(i, v);



}
# 369 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_sub_return_release(long i, atomic_long_t *v)
{

 return raw_atomic64_sub_return_release(i, v);



}
# 390 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_sub_return_relaxed(long i, atomic_long_t *v)
{

 return raw_atomic64_sub_return_relaxed(i, v);



}
# 411 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_sub(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_sub(i, v);



}
# 432 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_sub_acquire(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_sub_acquire(i, v);



}
# 453 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_sub_release(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_sub_release(i, v);



}
# 474 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_sub_relaxed(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_sub_relaxed(i, v);



}
# 494 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_long_inc(atomic_long_t *v)
{

 raw_atomic64_inc(v);



}
# 514 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_inc_return(atomic_long_t *v)
{

 return raw_atomic64_inc_return(v);



}
# 534 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_inc_return_acquire(atomic_long_t *v)
{

 return raw_atomic64_inc_return_acquire(v);



}
# 554 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_inc_return_release(atomic_long_t *v)
{

 return raw_atomic64_inc_return_release(v);



}
# 574 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_inc_return_relaxed(atomic_long_t *v)
{

 return raw_atomic64_inc_return_relaxed(v);



}
# 594 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_inc(atomic_long_t *v)
{

 return raw_atomic64_fetch_inc(v);



}
# 614 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_inc_acquire(atomic_long_t *v)
{

 return raw_atomic64_fetch_inc_acquire(v);



}
# 634 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_inc_release(atomic_long_t *v)
{

 return raw_atomic64_fetch_inc_release(v);



}
# 654 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_inc_relaxed(atomic_long_t *v)
{

 return raw_atomic64_fetch_inc_relaxed(v);



}
# 674 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_long_dec(atomic_long_t *v)
{

 raw_atomic64_dec(v);



}
# 694 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_dec_return(atomic_long_t *v)
{

 return raw_atomic64_dec_return(v);



}
# 714 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_dec_return_acquire(atomic_long_t *v)
{

 return raw_atomic64_dec_return_acquire(v);



}
# 734 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_dec_return_release(atomic_long_t *v)
{

 return raw_atomic64_dec_return_release(v);



}
# 754 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_dec_return_relaxed(atomic_long_t *v)
{

 return raw_atomic64_dec_return_relaxed(v);



}
# 774 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_dec(atomic_long_t *v)
{

 return raw_atomic64_fetch_dec(v);



}
# 794 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_dec_acquire(atomic_long_t *v)
{

 return raw_atomic64_fetch_dec_acquire(v);



}
# 814 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_dec_release(atomic_long_t *v)
{

 return raw_atomic64_fetch_dec_release(v);



}
# 834 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_dec_relaxed(atomic_long_t *v)
{

 return raw_atomic64_fetch_dec_relaxed(v);



}
# 855 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_long_and(long i, atomic_long_t *v)
{

 raw_atomic64_and(i, v);



}
# 876 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_and(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_and(i, v);



}
# 897 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_and_acquire(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_and_acquire(i, v);



}
# 918 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_and_release(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_and_release(i, v);



}
# 939 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_and_relaxed(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_and_relaxed(i, v);



}
# 960 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_long_andnot(long i, atomic_long_t *v)
{

 raw_atomic64_andnot(i, v);



}
# 981 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_andnot(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_andnot(i, v);



}
# 1002 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_andnot_acquire(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_andnot_acquire(i, v);



}
# 1023 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_andnot_release(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_andnot_release(i, v);



}
# 1044 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_andnot_relaxed(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_andnot_relaxed(i, v);



}
# 1065 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_long_or(long i, atomic_long_t *v)
{

 raw_atomic64_or(i, v);



}
# 1086 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_or(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_or(i, v);



}
# 1107 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_or_acquire(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_or_acquire(i, v);



}
# 1128 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_or_release(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_or_release(i, v);



}
# 1149 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_or_relaxed(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_or_relaxed(i, v);



}
# 1170 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
raw_atomic_long_xor(long i, atomic_long_t *v)
{

 raw_atomic64_xor(i, v);



}
# 1191 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_xor(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_xor(i, v);



}
# 1212 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_xor_acquire(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_xor_acquire(i, v);



}
# 1233 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_xor_release(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_xor_release(i, v);



}
# 1254 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_xor_relaxed(long i, atomic_long_t *v)
{

 return raw_atomic64_fetch_xor_relaxed(i, v);



}
# 1275 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_xchg(atomic_long_t *v, long new)
{

 return raw_atomic64_xchg(v, new);



}
# 1296 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_xchg_acquire(atomic_long_t *v, long new)
{

 return raw_atomic64_xchg_acquire(v, new);



}
# 1317 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_xchg_release(atomic_long_t *v, long new)
{

 return raw_atomic64_xchg_release(v, new);



}
# 1338 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_xchg_relaxed(atomic_long_t *v, long new)
{

 return raw_atomic64_xchg_relaxed(v, new);



}
# 1360 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_cmpxchg(atomic_long_t *v, long old, long new)
{

 return raw_atomic64_cmpxchg(v, old, new);



}
# 1382 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_cmpxchg_acquire(atomic_long_t *v, long old, long new)
{

 return raw_atomic64_cmpxchg_acquire(v, old, new);



}
# 1404 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_cmpxchg_release(atomic_long_t *v, long old, long new)
{

 return raw_atomic64_cmpxchg_release(v, old, new);



}
# 1426 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_cmpxchg_relaxed(atomic_long_t *v, long old, long new)
{

 return raw_atomic64_cmpxchg_relaxed(v, old, new);



}
# 1449 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_long_try_cmpxchg(atomic_long_t *v, long *old, long new)
{

 return raw_atomic64_try_cmpxchg(v, (s64 *)old, new);



}
# 1472 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_long_try_cmpxchg_acquire(atomic_long_t *v, long *old, long new)
{

 return raw_atomic64_try_cmpxchg_acquire(v, (s64 *)old, new);



}
# 1495 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_long_try_cmpxchg_release(atomic_long_t *v, long *old, long new)
{

 return raw_atomic64_try_cmpxchg_release(v, (s64 *)old, new);



}
# 1518 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_long_try_cmpxchg_relaxed(atomic_long_t *v, long *old, long new)
{

 return raw_atomic64_try_cmpxchg_relaxed(v, (s64 *)old, new);



}
# 1539 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_long_sub_and_test(long i, atomic_long_t *v)
{

 return raw_atomic64_sub_and_test(i, v);



}
# 1559 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_long_dec_and_test(atomic_long_t *v)
{

 return raw_atomic64_dec_and_test(v);



}
# 1579 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_long_inc_and_test(atomic_long_t *v)
{

 return raw_atomic64_inc_and_test(v);



}
# 1600 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_long_add_negative(long i, atomic_long_t *v)
{

 return raw_atomic64_add_negative(i, v);



}
# 1621 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_long_add_negative_acquire(long i, atomic_long_t *v)
{

 return raw_atomic64_add_negative_acquire(i, v);



}
# 1642 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_long_add_negative_release(long i, atomic_long_t *v)
{

 return raw_atomic64_add_negative_release(i, v);



}
# 1663 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_long_add_negative_relaxed(long i, atomic_long_t *v)
{

 return raw_atomic64_add_negative_relaxed(i, v);



}
# 1685 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_fetch_add_unless(atomic_long_t *v, long a, long u)
{

 return raw_atomic64_fetch_add_unless(v, a, u);



}
# 1707 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_long_add_unless(atomic_long_t *v, long a, long u)
{

 return raw_atomic64_add_unless(v, a, u);



}
# 1727 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_long_inc_not_zero(atomic_long_t *v)
{

 return raw_atomic64_inc_not_zero(v);



}
# 1747 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_long_inc_unless_negative(atomic_long_t *v)
{

 return raw_atomic64_inc_unless_negative(v);



}
# 1767 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
raw_atomic_long_dec_unless_positive(atomic_long_t *v)
{

 return raw_atomic64_dec_unless_positive(v);



}
# 1787 "./include/linux/atomic/atomic-long.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
raw_atomic_long_dec_if_positive(atomic_long_t *v)
{

 return raw_atomic64_dec_if_positive(v);



}
# 82 "./include/linux/atomic.h" 2
# 1 "./include/linux/atomic/atomic-instrumented.h" 1
# 17 "./include/linux/atomic/atomic-instrumented.h"
# 1 "./include/linux/instrumented.h" 1
# 13 "./include/linux/instrumented.h"
# 1 "./include/linux/kmsan-checks.h" 1
# 66 "./include/linux/kmsan-checks.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void kmsan_poison_memory(const void *address, size_t size,
           gfp_t flags)
{
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void kmsan_unpoison_memory(const void *address, size_t size)
{
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void kmsan_check_memory(const void *address, size_t size)
{
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void kmsan_copy_to_user(void *to, const void *from,
          size_t to_copy, size_t left)
{
}
# 14 "./include/linux/instrumented.h" 2
# 24 "./include/linux/instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void instrument_read(const volatile void *v, size_t size)
{
 kasan_check_read(v, size);
 kcsan_check_access(v, size, 0);
}
# 38 "./include/linux/instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void instrument_write(const volatile void *v, size_t size)
{
 kasan_check_write(v, size);
 kcsan_check_access(v, size, (1 << 0));
}
# 52 "./include/linux/instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void instrument_read_write(const volatile void *v, size_t size)
{
 kasan_check_write(v, size);
 kcsan_check_access(v, size, (1 << 1) | (1 << 0));
}
# 66 "./include/linux/instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void instrument_atomic_read(const volatile void *v, size_t size)
{
 kasan_check_read(v, size);
 kcsan_check_access(v, size, (1 << 2));
}
# 80 "./include/linux/instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void instrument_atomic_write(const volatile void *v, size_t size)
{
 kasan_check_write(v, size);
 kcsan_check_access(v, size, (1 << 2) | (1 << 0));
}
# 94 "./include/linux/instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void instrument_atomic_read_write(const volatile void *v, size_t size)
{
 kasan_check_write(v, size);
 kcsan_check_access(v, size, (1 << 2) | (1 << 0) | (1 << 1));
}
# 109 "./include/linux/instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
instrument_copy_to_user(void *to, const void *from, unsigned long n)
{
 kasan_check_read(from, n);
 kcsan_check_access(from, n, 0);
 kmsan_copy_to_user(to, from, n, 0);
}
# 126 "./include/linux/instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
instrument_copy_from_user_before(const void *to, const void *from, unsigned long n)
{
 kasan_check_write(to, n);
 kcsan_check_access(to, n, (1 << 0));
}
# 143 "./include/linux/instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
instrument_copy_from_user_after(const void *to, const void *from,
    unsigned long n, unsigned long left)
{
 kmsan_unpoison_memory(to, n - left);
}
# 18 "./include/linux/atomic/atomic-instrumented.h" 2
# 29 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_read(const atomic_t *v)
{
 instrument_atomic_read(v, sizeof(*v));
 return raw_atomic_read(v);
}
# 46 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_read_acquire(const atomic_t *v)
{
 instrument_atomic_read(v, sizeof(*v));
 return raw_atomic_read_acquire(v);
}
# 64 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_set(atomic_t *v, int i)
{
 instrument_atomic_write(v, sizeof(*v));
 raw_atomic_set(v, i);
}
# 82 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_set_release(atomic_t *v, int i)
{
 do { } while (0);
 instrument_atomic_write(v, sizeof(*v));
 raw_atomic_set_release(v, i);
}
# 101 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_add(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic_add(i, v);
}
# 119 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_add_return(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_add_return(i, v);
}
# 138 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_add_return_acquire(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_add_return_acquire(i, v);
}
# 156 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_add_return_release(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_add_return_release(i, v);
}
# 175 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_add_return_relaxed(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_add_return_relaxed(i, v);
}
# 193 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_add(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_add(i, v);
}
# 212 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_add_acquire(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_add_acquire(i, v);
}
# 230 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_add_release(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_add_release(i, v);
}
# 249 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_add_relaxed(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_add_relaxed(i, v);
}
# 267 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_sub(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic_sub(i, v);
}
# 285 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_sub_return(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_sub_return(i, v);
}
# 304 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_sub_return_acquire(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_sub_return_acquire(i, v);
}
# 322 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_sub_return_release(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_sub_return_release(i, v);
}
# 341 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_sub_return_relaxed(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_sub_return_relaxed(i, v);
}
# 359 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_sub(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_sub(i, v);
}
# 378 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_sub_acquire(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_sub_acquire(i, v);
}
# 396 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_sub_release(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_sub_release(i, v);
}
# 415 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_sub_relaxed(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_sub_relaxed(i, v);
}
# 432 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_inc(atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic_inc(v);
}
# 449 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_inc_return(atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_inc_return(v);
}
# 467 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_inc_return_acquire(atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_inc_return_acquire(v);
}
# 484 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_inc_return_release(atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_inc_return_release(v);
}
# 502 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_inc_return_relaxed(atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_inc_return_relaxed(v);
}
# 519 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_inc(atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_inc(v);
}
# 537 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_inc_acquire(atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_inc_acquire(v);
}
# 554 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_inc_release(atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_inc_release(v);
}
# 572 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_inc_relaxed(atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_inc_relaxed(v);
}
# 589 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_dec(atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic_dec(v);
}
# 606 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_dec_return(atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_dec_return(v);
}
# 624 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_dec_return_acquire(atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_dec_return_acquire(v);
}
# 641 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_dec_return_release(atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_dec_return_release(v);
}
# 659 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_dec_return_relaxed(atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_dec_return_relaxed(v);
}
# 676 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_dec(atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_dec(v);
}
# 694 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_dec_acquire(atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_dec_acquire(v);
}
# 711 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_dec_release(atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_dec_release(v);
}
# 729 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_dec_relaxed(atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_dec_relaxed(v);
}
# 747 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_and(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic_and(i, v);
}
# 765 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_and(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_and(i, v);
}
# 784 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_and_acquire(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_and_acquire(i, v);
}
# 802 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_and_release(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_and_release(i, v);
}
# 821 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_and_relaxed(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_and_relaxed(i, v);
}
# 839 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_andnot(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic_andnot(i, v);
}
# 857 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_andnot(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_andnot(i, v);
}
# 876 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_andnot_acquire(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_andnot_acquire(i, v);
}
# 894 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_andnot_release(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_andnot_release(i, v);
}
# 913 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_andnot_relaxed(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_andnot_relaxed(i, v);
}
# 931 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_or(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic_or(i, v);
}
# 949 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_or(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_or(i, v);
}
# 968 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_or_acquire(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_or_acquire(i, v);
}
# 986 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_or_release(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_or_release(i, v);
}
# 1005 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_or_relaxed(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_or_relaxed(i, v);
}
# 1023 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_xor(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic_xor(i, v);
}
# 1041 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_xor(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_xor(i, v);
}
# 1060 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_xor_acquire(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_xor_acquire(i, v);
}
# 1078 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_xor_release(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_xor_release(i, v);
}
# 1097 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_xor_relaxed(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_xor_relaxed(i, v);
}
# 1115 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_xchg(atomic_t *v, int new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_xchg(v, new);
}
# 1134 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_xchg_acquire(atomic_t *v, int new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_xchg_acquire(v, new);
}
# 1152 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_xchg_release(atomic_t *v, int new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_xchg_release(v, new);
}
# 1171 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_xchg_relaxed(atomic_t *v, int new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_xchg_relaxed(v, new);
}
# 1190 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_cmpxchg(atomic_t *v, int old, int new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_cmpxchg(v, old, new);
}
# 1210 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_cmpxchg_acquire(atomic_t *v, int old, int new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_cmpxchg_acquire(v, old, new);
}
# 1229 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_cmpxchg_release(atomic_t *v, int old, int new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_cmpxchg_release(v, old, new);
}
# 1249 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_cmpxchg_relaxed(atomic_t *v, int old, int new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_cmpxchg_relaxed(v, old, new);
}
# 1269 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_try_cmpxchg(atomic_t *v, int *old, int new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 instrument_atomic_read_write(old, sizeof(*old));
 return raw_atomic_try_cmpxchg(v, old, new);
}
# 1291 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_try_cmpxchg_acquire(atomic_t *v, int *old, int new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 instrument_atomic_read_write(old, sizeof(*old));
 return raw_atomic_try_cmpxchg_acquire(v, old, new);
}
# 1312 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_try_cmpxchg_release(atomic_t *v, int *old, int new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 instrument_atomic_read_write(old, sizeof(*old));
 return raw_atomic_try_cmpxchg_release(v, old, new);
}
# 1334 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_try_cmpxchg_relaxed(atomic_t *v, int *old, int new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 instrument_atomic_read_write(old, sizeof(*old));
 return raw_atomic_try_cmpxchg_relaxed(v, old, new);
}
# 1353 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_sub_and_test(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_sub_and_test(i, v);
}
# 1371 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_dec_and_test(atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_dec_and_test(v);
}
# 1389 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_inc_and_test(atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_inc_and_test(v);
}
# 1408 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_add_negative(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_add_negative(i, v);
}
# 1427 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_add_negative_acquire(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_add_negative_acquire(i, v);
}
# 1445 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_add_negative_release(int i, atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_add_negative_release(i, v);
}
# 1464 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_add_negative_relaxed(int i, atomic_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_add_negative_relaxed(i, v);
}
# 1483 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_fetch_add_unless(atomic_t *v, int a, int u)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_fetch_add_unless(v, a, u);
}
# 1503 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_add_unless(atomic_t *v, int a, int u)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_add_unless(v, a, u);
}
# 1521 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_inc_not_zero(atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_inc_not_zero(v);
}
# 1539 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_inc_unless_negative(atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_inc_unless_negative(v);
}
# 1557 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_dec_unless_positive(atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_dec_unless_positive(v);
}
# 1575 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int
atomic_dec_if_positive(atomic_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_dec_if_positive(v);
}
# 1593 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_read(const atomic64_t *v)
{
 instrument_atomic_read(v, sizeof(*v));
 return raw_atomic64_read(v);
}
# 1610 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_read_acquire(const atomic64_t *v)
{
 instrument_atomic_read(v, sizeof(*v));
 return raw_atomic64_read_acquire(v);
}
# 1628 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic64_set(atomic64_t *v, s64 i)
{
 instrument_atomic_write(v, sizeof(*v));
 raw_atomic64_set(v, i);
}
# 1646 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic64_set_release(atomic64_t *v, s64 i)
{
 do { } while (0);
 instrument_atomic_write(v, sizeof(*v));
 raw_atomic64_set_release(v, i);
}
# 1665 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic64_add(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic64_add(i, v);
}
# 1683 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_add_return(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_add_return(i, v);
}
# 1702 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_add_return_acquire(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_add_return_acquire(i, v);
}
# 1720 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_add_return_release(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_add_return_release(i, v);
}
# 1739 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_add_return_relaxed(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_add_return_relaxed(i, v);
}
# 1757 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_add(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_add(i, v);
}
# 1776 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_add_acquire(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_add_acquire(i, v);
}
# 1794 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_add_release(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_add_release(i, v);
}
# 1813 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_add_relaxed(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_add_relaxed(i, v);
}
# 1831 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic64_sub(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic64_sub(i, v);
}
# 1849 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_sub_return(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_sub_return(i, v);
}
# 1868 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_sub_return_acquire(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_sub_return_acquire(i, v);
}
# 1886 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_sub_return_release(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_sub_return_release(i, v);
}
# 1905 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_sub_return_relaxed(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_sub_return_relaxed(i, v);
}
# 1923 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_sub(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_sub(i, v);
}
# 1942 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_sub_acquire(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_sub_acquire(i, v);
}
# 1960 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_sub_release(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_sub_release(i, v);
}
# 1979 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_sub_relaxed(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_sub_relaxed(i, v);
}
# 1996 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic64_inc(atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic64_inc(v);
}
# 2013 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_inc_return(atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_inc_return(v);
}
# 2031 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_inc_return_acquire(atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_inc_return_acquire(v);
}
# 2048 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_inc_return_release(atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_inc_return_release(v);
}
# 2066 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_inc_return_relaxed(atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_inc_return_relaxed(v);
}
# 2083 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_inc(atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_inc(v);
}
# 2101 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_inc_acquire(atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_inc_acquire(v);
}
# 2118 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_inc_release(atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_inc_release(v);
}
# 2136 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_inc_relaxed(atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_inc_relaxed(v);
}
# 2153 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic64_dec(atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic64_dec(v);
}
# 2170 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_dec_return(atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_dec_return(v);
}
# 2188 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_dec_return_acquire(atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_dec_return_acquire(v);
}
# 2205 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_dec_return_release(atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_dec_return_release(v);
}
# 2223 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_dec_return_relaxed(atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_dec_return_relaxed(v);
}
# 2240 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_dec(atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_dec(v);
}
# 2258 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_dec_acquire(atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_dec_acquire(v);
}
# 2275 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_dec_release(atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_dec_release(v);
}
# 2293 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_dec_relaxed(atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_dec_relaxed(v);
}
# 2311 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic64_and(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic64_and(i, v);
}
# 2329 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_and(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_and(i, v);
}
# 2348 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_and_acquire(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_and_acquire(i, v);
}
# 2366 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_and_release(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_and_release(i, v);
}
# 2385 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_and_relaxed(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_and_relaxed(i, v);
}
# 2403 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic64_andnot(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic64_andnot(i, v);
}
# 2421 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_andnot(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_andnot(i, v);
}
# 2440 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_andnot_acquire(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_andnot_acquire(i, v);
}
# 2458 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_andnot_release(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_andnot_release(i, v);
}
# 2477 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_andnot_relaxed(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_andnot_relaxed(i, v);
}
# 2495 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic64_or(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic64_or(i, v);
}
# 2513 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_or(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_or(i, v);
}
# 2532 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_or_acquire(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_or_acquire(i, v);
}
# 2550 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_or_release(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_or_release(i, v);
}
# 2569 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_or_relaxed(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_or_relaxed(i, v);
}
# 2587 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic64_xor(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic64_xor(i, v);
}
# 2605 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_xor(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_xor(i, v);
}
# 2624 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_xor_acquire(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_xor_acquire(i, v);
}
# 2642 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_xor_release(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_xor_release(i, v);
}
# 2661 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_xor_relaxed(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_xor_relaxed(i, v);
}
# 2679 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_xchg(atomic64_t *v, s64 new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_xchg(v, new);
}
# 2698 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_xchg_acquire(atomic64_t *v, s64 new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_xchg_acquire(v, new);
}
# 2716 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_xchg_release(atomic64_t *v, s64 new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_xchg_release(v, new);
}
# 2735 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_xchg_relaxed(atomic64_t *v, s64 new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_xchg_relaxed(v, new);
}
# 2754 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_cmpxchg(atomic64_t *v, s64 old, s64 new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_cmpxchg(v, old, new);
}
# 2774 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_cmpxchg_acquire(atomic64_t *v, s64 old, s64 new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_cmpxchg_acquire(v, old, new);
}
# 2793 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_cmpxchg_release(atomic64_t *v, s64 old, s64 new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_cmpxchg_release(v, old, new);
}
# 2813 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_cmpxchg_relaxed(atomic64_t *v, s64 old, s64 new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_cmpxchg_relaxed(v, old, new);
}
# 2833 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic64_try_cmpxchg(atomic64_t *v, s64 *old, s64 new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 instrument_atomic_read_write(old, sizeof(*old));
 return raw_atomic64_try_cmpxchg(v, old, new);
}
# 2855 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic64_try_cmpxchg_acquire(atomic64_t *v, s64 *old, s64 new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 instrument_atomic_read_write(old, sizeof(*old));
 return raw_atomic64_try_cmpxchg_acquire(v, old, new);
}
# 2876 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic64_try_cmpxchg_release(atomic64_t *v, s64 *old, s64 new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 instrument_atomic_read_write(old, sizeof(*old));
 return raw_atomic64_try_cmpxchg_release(v, old, new);
}
# 2898 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic64_try_cmpxchg_relaxed(atomic64_t *v, s64 *old, s64 new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 instrument_atomic_read_write(old, sizeof(*old));
 return raw_atomic64_try_cmpxchg_relaxed(v, old, new);
}
# 2917 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic64_sub_and_test(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_sub_and_test(i, v);
}
# 2935 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic64_dec_and_test(atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_dec_and_test(v);
}
# 2953 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic64_inc_and_test(atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_inc_and_test(v);
}
# 2972 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic64_add_negative(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_add_negative(i, v);
}
# 2991 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic64_add_negative_acquire(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_add_negative_acquire(i, v);
}
# 3009 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic64_add_negative_release(s64 i, atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_add_negative_release(i, v);
}
# 3028 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic64_add_negative_relaxed(s64 i, atomic64_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_add_negative_relaxed(i, v);
}
# 3047 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_fetch_add_unless(atomic64_t *v, s64 a, s64 u)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_fetch_add_unless(v, a, u);
}
# 3067 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic64_add_unless(atomic64_t *v, s64 a, s64 u)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_add_unless(v, a, u);
}
# 3085 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic64_inc_not_zero(atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_inc_not_zero(v);
}
# 3103 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic64_inc_unless_negative(atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_inc_unless_negative(v);
}
# 3121 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic64_dec_unless_positive(atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_dec_unless_positive(v);
}
# 3139 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) s64
atomic64_dec_if_positive(atomic64_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic64_dec_if_positive(v);
}
# 3157 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_read(const atomic_long_t *v)
{
 instrument_atomic_read(v, sizeof(*v));
 return raw_atomic_long_read(v);
}
# 3174 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_read_acquire(const atomic_long_t *v)
{
 instrument_atomic_read(v, sizeof(*v));
 return raw_atomic_long_read_acquire(v);
}
# 3192 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_long_set(atomic_long_t *v, long i)
{
 instrument_atomic_write(v, sizeof(*v));
 raw_atomic_long_set(v, i);
}
# 3210 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_long_set_release(atomic_long_t *v, long i)
{
 do { } while (0);
 instrument_atomic_write(v, sizeof(*v));
 raw_atomic_long_set_release(v, i);
}
# 3229 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_long_add(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic_long_add(i, v);
}
# 3247 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_add_return(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_add_return(i, v);
}
# 3266 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_add_return_acquire(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_add_return_acquire(i, v);
}
# 3284 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_add_return_release(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_add_return_release(i, v);
}
# 3303 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_add_return_relaxed(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_add_return_relaxed(i, v);
}
# 3321 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_add(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_add(i, v);
}
# 3340 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_add_acquire(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_add_acquire(i, v);
}
# 3358 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_add_release(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_add_release(i, v);
}
# 3377 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_add_relaxed(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_add_relaxed(i, v);
}
# 3395 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_long_sub(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic_long_sub(i, v);
}
# 3413 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_sub_return(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_sub_return(i, v);
}
# 3432 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_sub_return_acquire(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_sub_return_acquire(i, v);
}
# 3450 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_sub_return_release(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_sub_return_release(i, v);
}
# 3469 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_sub_return_relaxed(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_sub_return_relaxed(i, v);
}
# 3487 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_sub(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_sub(i, v);
}
# 3506 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_sub_acquire(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_sub_acquire(i, v);
}
# 3524 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_sub_release(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_sub_release(i, v);
}
# 3543 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_sub_relaxed(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_sub_relaxed(i, v);
}
# 3560 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_long_inc(atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic_long_inc(v);
}
# 3577 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_inc_return(atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_inc_return(v);
}
# 3595 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_inc_return_acquire(atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_inc_return_acquire(v);
}
# 3612 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_inc_return_release(atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_inc_return_release(v);
}
# 3630 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_inc_return_relaxed(atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_inc_return_relaxed(v);
}
# 3647 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_inc(atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_inc(v);
}
# 3665 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_inc_acquire(atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_inc_acquire(v);
}
# 3682 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_inc_release(atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_inc_release(v);
}
# 3700 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_inc_relaxed(atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_inc_relaxed(v);
}
# 3717 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_long_dec(atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic_long_dec(v);
}
# 3734 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_dec_return(atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_dec_return(v);
}
# 3752 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_dec_return_acquire(atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_dec_return_acquire(v);
}
# 3769 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_dec_return_release(atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_dec_return_release(v);
}
# 3787 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_dec_return_relaxed(atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_dec_return_relaxed(v);
}
# 3804 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_dec(atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_dec(v);
}
# 3822 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_dec_acquire(atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_dec_acquire(v);
}
# 3839 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_dec_release(atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_dec_release(v);
}
# 3857 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_dec_relaxed(atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_dec_relaxed(v);
}
# 3875 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_long_and(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic_long_and(i, v);
}
# 3893 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_and(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_and(i, v);
}
# 3912 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_and_acquire(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_and_acquire(i, v);
}
# 3930 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_and_release(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_and_release(i, v);
}
# 3949 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_and_relaxed(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_and_relaxed(i, v);
}
# 3967 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_long_andnot(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic_long_andnot(i, v);
}
# 3985 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_andnot(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_andnot(i, v);
}
# 4004 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_andnot_acquire(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_andnot_acquire(i, v);
}
# 4022 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_andnot_release(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_andnot_release(i, v);
}
# 4041 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_andnot_relaxed(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_andnot_relaxed(i, v);
}
# 4059 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_long_or(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic_long_or(i, v);
}
# 4077 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_or(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_or(i, v);
}
# 4096 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_or_acquire(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_or_acquire(i, v);
}
# 4114 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_or_release(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_or_release(i, v);
}
# 4133 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_or_relaxed(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_or_relaxed(i, v);
}
# 4151 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) void
atomic_long_xor(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 raw_atomic_long_xor(i, v);
}
# 4169 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_xor(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_xor(i, v);
}
# 4188 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_xor_acquire(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_xor_acquire(i, v);
}
# 4206 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_xor_release(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_xor_release(i, v);
}
# 4225 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_xor_relaxed(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_xor_relaxed(i, v);
}
# 4243 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_xchg(atomic_long_t *v, long new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_xchg(v, new);
}
# 4262 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_xchg_acquire(atomic_long_t *v, long new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_xchg_acquire(v, new);
}
# 4280 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_xchg_release(atomic_long_t *v, long new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_xchg_release(v, new);
}
# 4299 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_xchg_relaxed(atomic_long_t *v, long new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_xchg_relaxed(v, new);
}
# 4318 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_cmpxchg(atomic_long_t *v, long old, long new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_cmpxchg(v, old, new);
}
# 4338 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_cmpxchg_acquire(atomic_long_t *v, long old, long new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_cmpxchg_acquire(v, old, new);
}
# 4357 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_cmpxchg_release(atomic_long_t *v, long old, long new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_cmpxchg_release(v, old, new);
}
# 4377 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_cmpxchg_relaxed(atomic_long_t *v, long old, long new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_cmpxchg_relaxed(v, old, new);
}
# 4397 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_long_try_cmpxchg(atomic_long_t *v, long *old, long new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 instrument_atomic_read_write(old, sizeof(*old));
 return raw_atomic_long_try_cmpxchg(v, old, new);
}
# 4419 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_long_try_cmpxchg_acquire(atomic_long_t *v, long *old, long new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 instrument_atomic_read_write(old, sizeof(*old));
 return raw_atomic_long_try_cmpxchg_acquire(v, old, new);
}
# 4440 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_long_try_cmpxchg_release(atomic_long_t *v, long *old, long new)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 instrument_atomic_read_write(old, sizeof(*old));
 return raw_atomic_long_try_cmpxchg_release(v, old, new);
}
# 4462 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_long_try_cmpxchg_relaxed(atomic_long_t *v, long *old, long new)
{
 instrument_atomic_read_write(v, sizeof(*v));
 instrument_atomic_read_write(old, sizeof(*old));
 return raw_atomic_long_try_cmpxchg_relaxed(v, old, new);
}
# 4481 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_long_sub_and_test(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_sub_and_test(i, v);
}
# 4499 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_long_dec_and_test(atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_dec_and_test(v);
}
# 4517 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_long_inc_and_test(atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_inc_and_test(v);
}
# 4536 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_long_add_negative(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_add_negative(i, v);
}
# 4555 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_long_add_negative_acquire(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_add_negative_acquire(i, v);
}
# 4573 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_long_add_negative_release(long i, atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_add_negative_release(i, v);
}
# 4592 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_long_add_negative_relaxed(long i, atomic_long_t *v)
{
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_add_negative_relaxed(i, v);
}
# 4611 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_fetch_add_unless(atomic_long_t *v, long a, long u)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_fetch_add_unless(v, a, u);
}
# 4631 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_long_add_unless(atomic_long_t *v, long a, long u)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_add_unless(v, a, u);
}
# 4649 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_long_inc_not_zero(atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_inc_not_zero(v);
}
# 4667 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_long_inc_unless_negative(atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_inc_unless_negative(v);
}
# 4685 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool
atomic_long_dec_unless_positive(atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_dec_unless_positive(v);
}
# 4703 "./include/linux/atomic/atomic-instrumented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) long
atomic_long_dec_if_positive(atomic_long_t *v)
{
 do { } while (0);
 instrument_atomic_read_write(v, sizeof(*v));
 return raw_atomic_long_dec_if_positive(v);
}
# 83 "./include/linux/atomic.h" 2
# 26 "./include/linux/rcupdate.h" 2
# 1 "./include/linux/irqflags.h" 1
# 15 "./include/linux/irqflags.h"
# 1 "./include/linux/irqflags_types.h" 1
# 16 "./include/linux/irqflags.h" 2
# 1 "./include/linux/typecheck.h" 1
# 17 "./include/linux/irqflags.h" 2
# 1 "./include/linux/cleanup.h" 1
# 71 "./include/linux/cleanup.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__warn_unused_result__))
const volatile void * __must_check_fn(const volatile void *val)
{ return val; }
# 18 "./include/linux/irqflags.h" 2
# 1 "./arch/x86/include/asm/irqflags.h" 1




# 1 "./arch/x86/include/asm/processor-flags.h" 1




# 1 "./arch/x86/include/uapi/asm/processor-flags.h" 1





# 1 "./include/linux/const.h" 1



# 1 "./include/vdso/const.h" 1




# 1 "./include/uapi/linux/const.h" 1
# 6 "./include/vdso/const.h" 2
# 5 "./include/linux/const.h" 2
# 7 "./arch/x86/include/uapi/asm/processor-flags.h" 2
# 6 "./arch/x86/include/asm/processor-flags.h" 2
# 1 "./include/linux/mem_encrypt.h" 1
# 17 "./include/linux/mem_encrypt.h"
# 1 "./arch/x86/include/asm/mem_encrypt.h" 1
# 15 "./arch/x86/include/asm/mem_encrypt.h"
# 1 "./include/linux/init.h" 1
# 115 "./include/linux/init.h"
typedef int (*initcall_t)(void);
typedef void (*exitcall_t)(void);


typedef int initcall_entry_t;

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) initcall_t initcall_from_entry(initcall_entry_t *entry)
{
 return offset_to_ptr(entry);
}
# 134 "./include/linux/init.h"
extern initcall_entry_t __con_initcall_start[], __con_initcall_end[];


typedef void (*ctor_fn_t)(void);

struct file_system_type;


extern int do_one_initcall(initcall_t fn);
extern char __attribute__((__section__(".init.data"))) boot_command_line[];
extern char *saved_command_line;
extern unsigned int saved_command_line_len;
extern unsigned int reset_devices;


void setup_arch(char **);
void prepare_namespace(void);
void __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep"))) init_rootfs(void);

void init_IRQ(void);
void time_init(void);
void poking_init(void);
void pgtable_cache_init(void);

extern initcall_entry_t __initcall_start[];
extern initcall_entry_t __initcall0_start[];
extern initcall_entry_t __initcall1_start[];
extern initcall_entry_t __initcall2_start[];
extern initcall_entry_t __initcall3_start[];
extern initcall_entry_t __initcall4_start[];
extern initcall_entry_t __initcall5_start[];
extern initcall_entry_t __initcall6_start[];
extern initcall_entry_t __initcall7_start[];
extern initcall_entry_t __initcall_end[];

extern struct file_system_type rootfs_fs_type;


extern bool rodata_enabled;


void mark_rodata_ro(void);


extern void (*late_time_init)(void);

extern bool initcall_debug;
# 327 "./include/linux/init.h"
struct obs_kernel_param {
 const char *str;
 int (*setup_func)(char *);
 int early;
};

extern const struct obs_kernel_param __setup_start[], __setup_end[];
# 385 "./include/linux/init.h"
void __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep"))) parse_early_param(void);
void __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep"))) parse_early_options(char *cmdline);
# 16 "./arch/x86/include/asm/mem_encrypt.h" 2
# 1 "./include/linux/cc_platform.h" 1
# 22 "./include/linux/cc_platform.h"
enum cc_attr {
# 33 "./include/linux/cc_platform.h"
 CC_ATTR_MEM_ENCRYPT,
# 43 "./include/linux/cc_platform.h"
 CC_ATTR_HOST_MEM_ENCRYPT,
# 53 "./include/linux/cc_platform.h"
 CC_ATTR_GUEST_MEM_ENCRYPT,
# 63 "./include/linux/cc_platform.h"
 CC_ATTR_GUEST_STATE_ENCRYPT,
# 74 "./include/linux/cc_platform.h"
 CC_ATTR_GUEST_UNROLL_STRING_IO,







 CC_ATTR_GUEST_SEV_SNP,
# 92 "./include/linux/cc_platform.h"
 CC_ATTR_HOTPLUG_DISABLED,
};
# 113 "./include/linux/cc_platform.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) bool cc_platform_has(enum cc_attr attr) { return false; }
# 17 "./arch/x86/include/asm/mem_encrypt.h" 2


struct boot_params;





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void mem_encrypt_init(void) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep"))) mem_encrypt_setup_arch(void) { }
# 74 "./arch/x86/include/asm/mem_encrypt.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep"))) sme_early_encrypt(resource_size_t paddr,
         unsigned long size) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep"))) sme_early_decrypt(resource_size_t paddr,
         unsigned long size) { }

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep"))) sme_map_bootdata(char *real_mode_data) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep"))) sme_unmap_bootdata(char *real_mode_data) { }

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep"))) sme_early_init(void) { }

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void sme_encrypt_kernel(struct boot_params *bp) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void sme_enable(struct boot_params *bp) { }

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void sev_es_init_vc_handling(void) { }

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) int __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep")))
early_set_memory_decrypted(unsigned long vaddr, unsigned long size) { return 0; }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) int __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep")))
early_set_memory_encrypted(unsigned long vaddr, unsigned long size) { return 0; }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep")))
early_set_mem_enc_dec_hypercall(unsigned long vaddr, unsigned long size, bool enc) {}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void mem_encrypt_free_decrypted_mem(void) { }

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) u64 sme_get_me_mask(void) { return 0; }





void add_encrypt_protection_map(void);
# 115 "./arch/x86/include/asm/mem_encrypt.h"
extern char __start_bss_decrypted[], __end_bss_decrypted[], __start_bss_decrypted_unused[];
# 18 "./include/linux/mem_encrypt.h" 2
# 7 "./arch/x86/include/asm/processor-flags.h" 2
# 6 "./arch/x86/include/asm/irqflags.h" 2



# 1 "./arch/x86/include/asm/nospec-branch.h" 1





# 1 "./include/linux/static_key.h" 1
# 1 "./include/linux/jump_label.h" 1
# 79 "./include/linux/jump_label.h"
extern bool static_key_initialized;





struct static_key {
 atomic_t enabled;
# 101 "./include/linux/jump_label.h"
 union {
  unsigned long type;
  struct jump_entry *entries;
  struct static_key_mod *next;
 };

};




# 1 "./arch/x86/include/asm/jump_label.h" 1
# 25 "./arch/x86/include/asm/jump_label.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool arch_static_branch(struct static_key *key, bool branch)
{
 asm goto("1:"
  "jmp %l[l_yes] # objtool NOPs this \n\t"
  ".pushsection __jump_table,  \"aw\" \n\t" " " ".balign 8" " " "\n\t" ".long 1b - . \n\t" ".long %l[l_yes] - . \n\t" " " ".quad" " " "%c0 + %c1 - .\n\t" ".popsection \n\t"
  : : "i" (key), "i" (2 | branch) : : l_yes);

 return false;
l_yes:
 return true;
}
# 53 "./arch/x86/include/asm/jump_label.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool arch_static_branch_jump(struct static_key * const key, const bool branch)
{
 asm goto("1:"
  "jmp %l[l_yes]\n\t"
  ".pushsection __jump_table,  \"aw\" \n\t" " " ".balign 8" " " "\n\t" ".long 1b - . \n\t" ".long %l[l_yes] - . \n\t" " " ".quad" " " "%c0 + %c1 - .\n\t" ".popsection \n\t"
  : : "i" (key), "i" (branch) : : l_yes);

 return false;
l_yes:
 return true;
}

extern int arch_jump_entry_size(struct jump_entry *entry);
# 113 "./include/linux/jump_label.h" 2




struct jump_entry {
 s32 code;
 s32 target;
 long key;
};

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) unsigned long jump_entry_code(const struct jump_entry *entry)
{
 return (unsigned long)&entry->code + entry->code;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) unsigned long jump_entry_target(const struct jump_entry *entry)
{
 return (unsigned long)&entry->target + entry->target;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) struct static_key *jump_entry_key(const struct jump_entry *entry)
{
 long offset = entry->key & ~3L;

 return (struct static_key *)((unsigned long)&entry->key + offset);
}
# 159 "./include/linux/jump_label.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) bool jump_entry_is_branch(const struct jump_entry *entry)
{
 return (unsigned long)entry->key & 1UL;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) bool jump_entry_is_init(const struct jump_entry *entry)
{
 return (unsigned long)entry->key & 2UL;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) void jump_entry_set_init(struct jump_entry *entry, bool set)
{
 if (set)
  entry->key |= 2;
 else
  entry->key &= ~2;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) int jump_entry_size(struct jump_entry *entry)
{



 return arch_jump_entry_size(entry);

}






enum jump_label_type {
 JUMP_LABEL_NOP = 0,
 JUMP_LABEL_JMP,
};

struct module;
# 205 "./include/linux/jump_label.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool static_key_false(struct static_key *key)
{
 return arch_static_branch(key, false);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) bool static_key_true(struct static_key *key)
{
 return !arch_static_branch(key, true);
}

extern struct jump_entry __start___jump_table[];
extern struct jump_entry __stop___jump_table[];

extern void jump_label_init(void);
extern void jump_label_lock(void);
extern void jump_label_unlock(void);
extern void arch_jump_label_transform(struct jump_entry *entry,
          enum jump_label_type type);
extern bool arch_jump_label_transform_queue(struct jump_entry *entry,
         enum jump_label_type type);
extern void arch_jump_label_transform_apply(void);
extern int jump_label_text_reserved(void *start, void *end);
extern bool static_key_slow_inc(struct static_key *key);
extern bool static_key_fast_inc_not_disabled(struct static_key *key);
extern void static_key_slow_dec(struct static_key *key);
extern bool static_key_slow_inc_cpuslocked(struct static_key *key);
extern void static_key_slow_dec_cpuslocked(struct static_key *key);
extern int static_key_count(struct static_key *key);
extern void static_key_enable(struct static_key *key);
extern void static_key_disable(struct static_key *key);
extern void static_key_enable_cpuslocked(struct static_key *key);
extern void static_key_disable_cpuslocked(struct static_key *key);
extern enum jump_label_type jump_label_init_type(struct jump_entry *entry);
# 359 "./include/linux/jump_label.h"
struct static_key_true {
 struct static_key key;
};

struct static_key_false {
 struct static_key key;
};
# 413 "./include/linux/jump_label.h"
extern bool ____wrong_branch_error(void);
# 2 "./include/linux/static_key.h" 2
# 7 "./arch/x86/include/asm/nospec-branch.h" 2
# 1 "./include/linux/objtool.h" 1




# 1 "./include/linux/objtool_types.h" 1
# 13 "./include/linux/objtool_types.h"
struct unwind_hint {
 u32 ip;
 s16 sp_offset;
 u8 sp_reg;
 u8 type;
 u8 signal;
};
# 6 "./include/linux/objtool.h" 2
# 8 "./arch/x86/include/asm/nospec-branch.h" 2
# 1 "./include/linux/linkage.h" 1






# 1 "./include/linux/export.h" 1





# 1 "./include/linux/linkage.h" 1
# 7 "./include/linux/export.h" 2
# 8 "./include/linux/linkage.h" 2
# 1 "./arch/x86/include/asm/linkage.h" 1





# 1 "./arch/x86/include/asm/ibt.h" 1
# 44 "./arch/x86/include/asm/ibt.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__const__)) u32 gen_endbr(void)
{
 u32 endbr;





 asm ( "mov $~0xfa1e0ff3, %[endbr]\n\t"
       "not %[endbr]\n\t"
        : [endbr] "=&r" (endbr) );

 return endbr;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__const__)) u32 gen_endbr_poison(void)
{




 return 0x001f0f66;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) bool is_endbr(u32 val)
{
 if (val == gen_endbr_poison())
  return true;

 val &= ~0x01000000U;
 return val == gen_endbr();
}

extern __attribute__((nocf_check)) u64 ibt_save(bool disable);
extern __attribute__((nocf_check)) void ibt_restore(u64 save);
# 7 "./arch/x86/include/asm/linkage.h" 2
# 9 "./include/linux/linkage.h" 2
# 9 "./arch/x86/include/asm/nospec-branch.h" 2



# 1 "./arch/x86/include/asm/msr-index.h" 1




# 1 "./include/linux/bits.h" 1





# 1 "./include/vdso/bits.h" 1
# 7 "./include/linux/bits.h" 2
# 6 "./arch/x86/include/asm/msr-index.h" 2
# 13 "./arch/x86/include/asm/nospec-branch.h" 2
# 1 "./arch/x86/include/asm/unwind_hints.h" 1





# 1 "./arch/x86/include/asm/orc_types.h" 1
# 49 "./arch/x86/include/asm/orc_types.h"
# 1 "./arch/x86/include/uapi/asm/byteorder.h" 1




# 1 "./include/linux/byteorder/little_endian.h" 1




# 1 "./include/uapi/linux/byteorder/little_endian.h" 1
# 14 "./include/uapi/linux/byteorder/little_endian.h"
# 1 "./include/linux/swab.h" 1




# 1 "./include/uapi/linux/swab.h" 1







# 1 "./arch/x86/include/uapi/asm/swab.h" 1







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__const__)) __u32 __arch_swab32(__u32 val)
{
 asm("bswapl %0" : "=r" (val) : "0" (val));
 return val;
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__const__)) __u64 __arch_swab64(__u64 val)
{
# 31 "./arch/x86/include/uapi/asm/swab.h"
 asm("bswapq %0" : "=r" (val) : "0" (val));
 return val;

}
# 9 "./include/uapi/linux/swab.h" 2
# 48 "./include/uapi/linux/swab.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__const__)) __u16 __fswab16(__u16 val)
{



 return ((__u16)( (((__u16)(val) & (__u16)0x00ffU) << 8) | (((__u16)(val) & (__u16)0xff00U) >> 8)));

}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__const__)) __u32 __fswab32(__u32 val)
{

 return __arch_swab32(val);



}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__const__)) __u64 __fswab64(__u64 val)
{

 return __arch_swab64(val);







}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__const__)) __u32 __fswahw32(__u32 val)
{



 return ((__u32)( (((__u32)(val) & (__u32)0x0000ffffUL) << 16) | (((__u32)(val) & (__u32)0xffff0000UL) >> 16)));

}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__const__)) __u32 __fswahb32(__u32 val)
{



 return ((__u32)( (((__u32)(val) & (__u32)0x00ff00ffUL) << 8) | (((__u32)(val) & (__u32)0xff00ff00UL) >> 8)));

}
# 136 "./include/uapi/linux/swab.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long __swab(const unsigned long y)
{

 return (__u64)__builtin_bswap64((__u64)(y));



}
# 171 "./include/uapi/linux/swab.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __u16 __swab16p(const __u16 *p)
{



 return (__u16)__builtin_bswap16((__u16)(*p));

}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __u32 __swab32p(const __u32 *p)
{



 return (__u32)__builtin_bswap32((__u32)(*p));

}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __u64 __swab64p(const __u64 *p)
{



 return (__u64)__builtin_bswap64((__u64)(*p));

}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __u32 __swahw32p(const __u32 *p)
{



 return (__builtin_constant_p((__u32)(*p)) ? ((__u32)( (((__u32)(*p) & (__u32)0x0000ffffUL) << 16) | (((__u32)(*p) & (__u32)0xffff0000UL) >> 16))) : __fswahw32(*p));

}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __u32 __swahb32p(const __u32 *p)
{



 return (__builtin_constant_p((__u32)(*p)) ? ((__u32)( (((__u32)(*p) & (__u32)0x00ff00ffUL) << 8) | (((__u32)(*p) & (__u32)0xff00ff00UL) >> 8))) : __fswahb32(*p));

}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __swab16s(__u16 *p)
{



 *p = __swab16p(p);

}




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void __swab32s(__u32 *p)
{



 *p = __swab32p(p);

}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void __swab64s(__u64 *p)
{



 *p = __swab64p(p);

}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __swahw32s(__u32 *p)
{



 *p = __swahw32p(p);

}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __swahb32s(__u32 *p)
{



 *p = __swahb32p(p);

}
# 6 "./include/linux/swab.h" 2
# 24 "./include/linux/swab.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void swab16_array(u16 *buf, unsigned int words)
{
 while (words--) {
  __swab16s(buf);
  buf++;
 }
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void swab32_array(u32 *buf, unsigned int words)
{
 while (words--) {
  __swab32s(buf);
  buf++;
 }
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void swab64_array(u64 *buf, unsigned int words)
{
 while (words--) {
  __swab64s(buf);
  buf++;
 }
}
# 15 "./include/uapi/linux/byteorder/little_endian.h" 2
# 45 "./include/uapi/linux/byteorder/little_endian.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __le64 __cpu_to_le64p(const __u64 *p)
{
 return ( __le64)*p;
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __u64 __le64_to_cpup(const __le64 *p)
{
 return ( __u64)*p;
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __le32 __cpu_to_le32p(const __u32 *p)
{
 return ( __le32)*p;
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __u32 __le32_to_cpup(const __le32 *p)
{
 return ( __u32)*p;
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __le16 __cpu_to_le16p(const __u16 *p)
{
 return ( __le16)*p;
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __u16 __le16_to_cpup(const __le16 *p)
{
 return ( __u16)*p;
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __be64 __cpu_to_be64p(const __u64 *p)
{
 return ( __be64)__swab64p(p);
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __u64 __be64_to_cpup(const __be64 *p)
{
 return __swab64p((__u64 *)p);
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __be32 __cpu_to_be32p(const __u32 *p)
{
 return ( __be32)__swab32p(p);
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __u32 __be32_to_cpup(const __be32 *p)
{
 return __swab32p((__u32 *)p);
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __be16 __cpu_to_be16p(const __u16 *p)
{
 return ( __be16)__swab16p(p);
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __u16 __be16_to_cpup(const __be16 *p)
{
 return __swab16p((__u16 *)p);
}
# 6 "./include/linux/byteorder/little_endian.h" 2





# 1 "./include/linux/byteorder/generic.h" 1
# 144 "./include/linux/byteorder/generic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void le16_add_cpu(__le16 *var, u16 val)
{
 *var = (( __le16)(__u16)((( __u16)(__le16)(*var)) + val));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void le32_add_cpu(__le32 *var, u32 val)
{
 *var = (( __le32)(__u32)((( __u32)(__le32)(*var)) + val));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void le64_add_cpu(__le64 *var, u64 val)
{
 *var = (( __le64)(__u64)((( __u64)(__le64)(*var)) + val));
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void le32_to_cpu_array(u32 *buf, unsigned int words)
{
 while (words--) {
  do { (void)(buf); } while (0);
  buf++;
 }
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void cpu_to_le32_array(u32 *buf, unsigned int words)
{
 while (words--) {
  do { (void)(buf); } while (0);
  buf++;
 }
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void be16_add_cpu(__be16 *var, u16 val)
{
 *var = (( __be16)(__u16)__builtin_bswap16((__u16)(((__u16)__builtin_bswap16((__u16)(( __u16)(__be16)(*var))) + val))));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void be32_add_cpu(__be32 *var, u32 val)
{
 *var = (( __be32)(__u32)__builtin_bswap32((__u32)(((__u32)__builtin_bswap32((__u32)(( __u32)(__be32)(*var))) + val))));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void be64_add_cpu(__be64 *var, u64 val)
{
 *var = (( __be64)(__u64)__builtin_bswap64((__u64)(((__u64)__builtin_bswap64((__u64)(( __u64)(__be64)(*var))) + val))));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void cpu_to_be32_array(__be32 *dst, const u32 *src, size_t len)
{
 size_t i;

 for (i = 0; i < len; i++)
  dst[i] = (( __be32)(__u32)__builtin_bswap32((__u32)((src[i]))));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void be32_to_cpu_array(u32 *dst, const __be32 *src, size_t len)
{
 size_t i;

 for (i = 0; i < len; i++)
  dst[i] = (__u32)__builtin_bswap32((__u32)(( __u32)(__be32)(src[i])));
}
# 12 "./include/linux/byteorder/little_endian.h" 2
# 6 "./arch/x86/include/uapi/asm/byteorder.h" 2
# 50 "./arch/x86/include/asm/orc_types.h" 2
# 59 "./arch/x86/include/asm/orc_types.h"
struct orc_entry {
 s16 sp_offset;
 s16 bp_offset;

 unsigned sp_reg:4;
 unsigned bp_reg:4;
 unsigned type:3;
 unsigned signal:1;







} __attribute__((__packed__));
# 7 "./arch/x86/include/asm/unwind_hints.h" 2
# 14 "./arch/x86/include/asm/nospec-branch.h" 2
# 1 "./arch/x86/include/asm/percpu.h" 1
# 476 "./arch/x86/include/asm/percpu.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool x86_this_cpu_constant_test_bit(unsigned int nr,
                        const unsigned long *addr)
{
 unsigned long *a =
  (unsigned long *)addr + nr / 64;


 return ((1UL << (nr % 64)) & ({ u64 pfo_val__; asm ("mov" "q " "%%""gs"":" "%" "[var]" ", " "%[val]" : [val] "=" "r" (pfo_val__) : [var] "m" (*a)); (typeof(*a))(unsigned long) pfo_val__; })) != 0;



}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool x86_this_cpu_variable_test_bit(int nr,
                        const unsigned long *addr)
{
 bool oldbit;

 asm volatile("btl ""%%""gs"":" "%" "2"",%1"
   "\n\t/* output condition code " "c" "*/\n"
   : "=@cc" "c" (oldbit)
   : "m" (*(unsigned long *)addr), "Ir" (nr));

 return oldbit;
}







# 1 "./include/asm-generic/percpu.h" 1





# 1 "./include/linux/threads.h" 1
# 7 "./include/asm-generic/percpu.h" 2
# 1 "./include/linux/percpu-defs.h" 1
# 308 "./include/linux/percpu-defs.h"
extern void __bad_size_call_parameter(void);




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void __this_cpu_preempt_check(const char *op) { }
# 8 "./include/asm-generic/percpu.h" 2
# 19 "./include/asm-generic/percpu.h"
extern unsigned long __per_cpu_offset[64];
# 48 "./include/asm-generic/percpu.h"
extern void setup_per_cpu_areas(void);
# 509 "./arch/x86/include/asm/percpu.h" 2


extern __attribute__((section(".data..percpu" "..read_mostly"))) __typeof__(unsigned long) this_cpu_off;
# 15 "./arch/x86/include/asm/nospec-branch.h" 2
# 1 "./arch/x86/include/asm/current.h" 1
# 10 "./arch/x86/include/asm/current.h"
# 1 "./include/linux/cache.h" 1




# 1 "./include/uapi/linux/kernel.h" 1




# 1 "./include/uapi/linux/sysinfo.h" 1







struct sysinfo {
 __kernel_long_t uptime;
 __kernel_ulong_t loads[3];
 __kernel_ulong_t totalram;
 __kernel_ulong_t freeram;
 __kernel_ulong_t sharedram;
 __kernel_ulong_t bufferram;
 __kernel_ulong_t totalswap;
 __kernel_ulong_t freeswap;
 __u16 procs;
 __u16 pad;
 __kernel_ulong_t totalhigh;
 __kernel_ulong_t freehigh;
 __u32 mem_unit;
 char _f[20-2*sizeof(__kernel_ulong_t)-sizeof(__u32)];
};
# 6 "./include/uapi/linux/kernel.h" 2
# 6 "./include/linux/cache.h" 2
# 1 "./arch/x86/include/asm/cache.h" 1
# 7 "./include/linux/cache.h" 2
# 118 "./include/linux/cache.h"
struct cacheline_padding {
 char x[0];
} __attribute__((__aligned__(1 << (6))));
# 11 "./arch/x86/include/asm/current.h" 2


struct task_struct;

struct pcpu_hot {
 union {
  struct {
   struct task_struct *current_task;
   int preempt_count;
   int cpu_number;

   u64 call_depth;

   unsigned long top_of_stack;
   void *hardirq_stack_ptr;
   u16 softirq_pending;

   bool hardirq_stack_inuse;



  };
  u8 pad[64];
 };
};
_Static_assert(sizeof(struct pcpu_hot) == 64, "sizeof(struct pcpu_hot) == 64");

extern __attribute__((section(".data..percpu" "..shared_aligned"))) __typeof__(struct pcpu_hot) pcpu_hot __attribute__((__aligned__((1 << (6)))));

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) struct task_struct *get_current(void)
{
 return ({ typeof(pcpu_hot.current_task) pscr_ret__; do { const void *__vpp_verify = (typeof((&(pcpu_hot.current_task)) + 0))((void *)0); (void)__vpp_verify; } while (0); switch(sizeof(pcpu_hot.current_task)) { case 1: pscr_ret__ = ({ u8 pfo_val__; asm("mov" "b " "%%""gs"":" "%" "P[var]" ", " "%[val]" : [val] "=" "q" (pfo_val__) : [var] "p" (&(pcpu_hot.current_task))); (typeof(pcpu_hot.current_task))(unsigned long) pfo_val__; }); break; case 2: pscr_ret__ = ({ u16 pfo_val__; asm("mov" "w " "%%""gs"":" "%" "P[var]" ", " "%[val]" : [val] "=" "r" (pfo_val__) : [var] "p" (&(pcpu_hot.current_task))); (typeof(pcpu_hot.current_task))(unsigned long) pfo_val__; }); break; case 4: pscr_ret__ = ({ u32 pfo_val__; asm("mov" "l " "%%""gs"":" "%" "P[var]" ", " "%[val]" : [val] "=" "r" (pfo_val__) : [var] "p" (&(pcpu_hot.current_task))); (typeof(pcpu_hot.current_task))(unsigned long) pfo_val__; }); break; case 8: pscr_ret__ = ({ u64 pfo_val__; asm("mov" "q " "%%""gs"":" "%" "P[var]" ", " "%[val]" : [val] "=" "r" (pfo_val__) : [var] "p" (&(pcpu_hot.current_task))); (typeof(pcpu_hot.current_task))(unsigned long) pfo_val__; }); break; default: __bad_size_call_parameter(); break; } pscr_ret__; });
}
# 16 "./arch/x86/include/asm/nospec-branch.h" 2
# 78 "./arch/x86/include/asm/nospec-branch.h"
# 1 "./arch/x86/include/asm/asm-offsets.h" 1
# 1 "./include/generated/asm-offsets.h" 1
# 2 "./arch/x86/include/asm/asm-offsets.h" 2
# 79 "./arch/x86/include/asm/nospec-branch.h" 2
# 359 "./arch/x86/include/asm/nospec-branch.h"
typedef u8 retpoline_thunk_t[32];
extern retpoline_thunk_t __x86_indirect_thunk_array[];
extern retpoline_thunk_t __x86_indirect_call_thunk_array[];
extern retpoline_thunk_t __x86_indirect_jump_thunk_array[];


extern void __x86_return_thunk(void);





extern void retbleed_return_thunk(void);




extern void srso_alias_untrain_ret(void);


extern void srso_return_thunk(void);
extern void srso_alias_return_thunk(void);





extern void retbleed_return_thunk(void);
extern void srso_return_thunk(void);
extern void srso_alias_return_thunk(void);

extern void entry_untrain_ret(void);
extern void entry_ibpb(void);


extern void clear_bhb_loop(void);


extern void (*x86_return_thunk)(void);


extern void call_depth_return_thunk(void);
# 424 "./arch/x86/include/asm/nospec-branch.h"
# 1 "./arch/x86/include/asm/GEN-for-each-reg.h" 1





extern retpoline_thunk_t __x86_indirect_thunk_rax;
extern retpoline_thunk_t __x86_indirect_thunk_rcx;
extern retpoline_thunk_t __x86_indirect_thunk_rdx;
extern retpoline_thunk_t __x86_indirect_thunk_rbx;
extern retpoline_thunk_t __x86_indirect_thunk_rsp;
extern retpoline_thunk_t __x86_indirect_thunk_rbp;
extern retpoline_thunk_t __x86_indirect_thunk_rsi;
extern retpoline_thunk_t __x86_indirect_thunk_rdi;
extern retpoline_thunk_t __x86_indirect_thunk_r8;
extern retpoline_thunk_t __x86_indirect_thunk_r9;
extern retpoline_thunk_t __x86_indirect_thunk_r10;
extern retpoline_thunk_t __x86_indirect_thunk_r11;
extern retpoline_thunk_t __x86_indirect_thunk_r12;
extern retpoline_thunk_t __x86_indirect_thunk_r13;
extern retpoline_thunk_t __x86_indirect_thunk_r14;
extern retpoline_thunk_t __x86_indirect_thunk_r15;
# 425 "./arch/x86/include/asm/nospec-branch.h" 2




# 1 "./arch/x86/include/asm/GEN-for-each-reg.h" 1





extern retpoline_thunk_t __x86_indirect_call_thunk_rax;
extern retpoline_thunk_t __x86_indirect_call_thunk_rcx;
extern retpoline_thunk_t __x86_indirect_call_thunk_rdx;
extern retpoline_thunk_t __x86_indirect_call_thunk_rbx;
extern retpoline_thunk_t __x86_indirect_call_thunk_rsp;
extern retpoline_thunk_t __x86_indirect_call_thunk_rbp;
extern retpoline_thunk_t __x86_indirect_call_thunk_rsi;
extern retpoline_thunk_t __x86_indirect_call_thunk_rdi;
extern retpoline_thunk_t __x86_indirect_call_thunk_r8;
extern retpoline_thunk_t __x86_indirect_call_thunk_r9;
extern retpoline_thunk_t __x86_indirect_call_thunk_r10;
extern retpoline_thunk_t __x86_indirect_call_thunk_r11;
extern retpoline_thunk_t __x86_indirect_call_thunk_r12;
extern retpoline_thunk_t __x86_indirect_call_thunk_r13;
extern retpoline_thunk_t __x86_indirect_call_thunk_r14;
extern retpoline_thunk_t __x86_indirect_call_thunk_r15;
# 430 "./arch/x86/include/asm/nospec-branch.h" 2




# 1 "./arch/x86/include/asm/GEN-for-each-reg.h" 1





extern retpoline_thunk_t __x86_indirect_jump_thunk_rax;
extern retpoline_thunk_t __x86_indirect_jump_thunk_rcx;
extern retpoline_thunk_t __x86_indirect_jump_thunk_rdx;
extern retpoline_thunk_t __x86_indirect_jump_thunk_rbx;
extern retpoline_thunk_t __x86_indirect_jump_thunk_rsp;
extern retpoline_thunk_t __x86_indirect_jump_thunk_rbp;
extern retpoline_thunk_t __x86_indirect_jump_thunk_rsi;
extern retpoline_thunk_t __x86_indirect_jump_thunk_rdi;
extern retpoline_thunk_t __x86_indirect_jump_thunk_r8;
extern retpoline_thunk_t __x86_indirect_jump_thunk_r9;
extern retpoline_thunk_t __x86_indirect_jump_thunk_r10;
extern retpoline_thunk_t __x86_indirect_jump_thunk_r11;
extern retpoline_thunk_t __x86_indirect_jump_thunk_r12;
extern retpoline_thunk_t __x86_indirect_jump_thunk_r13;
extern retpoline_thunk_t __x86_indirect_jump_thunk_r14;
extern retpoline_thunk_t __x86_indirect_jump_thunk_r15;
# 435 "./arch/x86/include/asm/nospec-branch.h" 2
# 492 "./arch/x86/include/asm/nospec-branch.h"
enum spectre_v2_mitigation {
 SPECTRE_V2_NONE,
 SPECTRE_V2_RETPOLINE,
 SPECTRE_V2_LFENCE,
 SPECTRE_V2_EIBRS,
 SPECTRE_V2_EIBRS_RETPOLINE,
 SPECTRE_V2_EIBRS_LFENCE,
 SPECTRE_V2_IBRS,
};


enum spectre_v2_user_mitigation {
 SPECTRE_V2_USER_NONE,
 SPECTRE_V2_USER_STRICT,
 SPECTRE_V2_USER_STRICT_PREFERRED,
 SPECTRE_V2_USER_PRCTL,
 SPECTRE_V2_USER_SECCOMP,
};


enum ssb_mitigation {
 SPEC_STORE_BYPASS_NONE,
 SPEC_STORE_BYPASS_DISABLE,
 SPEC_STORE_BYPASS_PRCTL,
 SPEC_STORE_BYPASS_SECCOMP,
};

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__))
void alternative_msr_write(unsigned int msr, u64 val, unsigned int feature)
{
 asm volatile("# ALT: oldnstr\n" "661:\n\t" "" "\n662:\n" "# ALT: padding\n" ".skip -(((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")) > 0) * " "((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")),0x90\n" "663" ":\n" ".pushsection .altinstructions,\"a\"\n" " .long 661b - .\n" " .long " "664""1""f - .\n" " .4byte " "%c[feature]" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""1""f-""664""1""f" "\n" ".popsection\n" ".pushsection .altinstr_replacement, \"ax\"\n" "# ALT: replacement " "1" "\n" "664""1"":\n\t" "wrmsr" "\n" "665""1" ":\n" ".popsection\n"
  : : "c" (msr),
      "a" ((u32)val),
      "d" ((u32)(val >> 32)),
      [feature] "i" (feature)
  : "memory");
}

extern u64 x86_pred_cmd;

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void indirect_branch_prediction_barrier(void)
{
 alternative_msr_write(0x00000049, x86_pred_cmd, ( 7*32+21));
}


extern u64 x86_spec_ctrl_base;
extern __attribute__((section(".data..percpu" ""))) __typeof__(u64) x86_spec_ctrl_current;
extern void update_spec_ctrl_cond(u64 val);
extern u64 spec_ctrl_current(void);
# 567 "./arch/x86/include/asm/nospec-branch.h"
extern struct static_key_false switch_to_cond_stibp;
extern struct static_key_false switch_mm_cond_ibpb;
extern struct static_key_false switch_mm_always_ibpb;

extern struct static_key_false mds_idle_clear;

extern struct static_key_false switch_mm_cond_l1d_flush;

extern struct static_key_false mmio_stale_data_clear;

extern u16 mds_verw_sel;

# 1 "./arch/x86/include/asm/segment.h" 1
# 240 "./arch/x86/include/asm/segment.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long vdso_encode_cpunode(int cpu, unsigned long node)
{
 return (node << 12) | cpu;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void vdso_read_cpunode(unsigned *cpu, unsigned *node)
{
 unsigned int p;
# 257 "./arch/x86/include/asm/segment.h"
 asm __inline volatile ("# ALT: oldnstr\n" "661:\n\t" "lsl %[seg],%[p]" "\n662:\n" "# ALT: padding\n" ".skip -(((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")) > 0) * " "((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")),0x90\n" "663" ":\n" ".pushsection .altinstructions,\"a\"\n" " .long 661b - .\n" " .long " "664""1""f - .\n" " .4byte " "(16*32+22)" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""1""f-""664""1""f" "\n" ".popsection\n" ".pushsection .altinstr_replacement, \"ax\"\n" "# ALT: replacement " "1" "\n" "664""1"":\n\t" ".byte 0xf3,0x0f,0xc7,0xf8" "\n" "665""1" ":\n" ".popsection\n" : [p] "=a" (p) : "i" (0), [seg] "r" ((15*8 + 3)))


                                           ;

 if (cpu)
  *cpu = (p & 0xfff);
 if (node)
  *node = (p >> 12);
}
# 291 "./arch/x86/include/asm/segment.h"
extern const char early_idt_handler_array[32][(9 + (4*1))];
extern void early_ignore_irq(void);
# 330 "./arch/x86/include/asm/segment.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __loadsegment_fs(unsigned short value)
{
 asm volatile("						\n"
       "1:	movw %0, %%fs			\n"
       "2:					\n"

       " .pushsection \"__ex_table\",\"a\"\n" " .balign 4\n" " .long (" "1b" ") - .\n" " .long (" "2b" ") - .\n" " .long " "5" " \n" " .popsection\n"

       : : "rm" (value) : "memory");
}
# 580 "./arch/x86/include/asm/nospec-branch.h" 2
# 588 "./arch/x86/include/asm/nospec-branch.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void mds_clear_cpu_buffers(void)
{
 static const u16 ds = (3*8);
# 601 "./arch/x86/include/asm/nospec-branch.h"
 asm volatile("verw %[ds]" : : [ds] "m" (ds) : "cc");
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void mds_idle_clear_cpu_buffers(void)
{
 if (({ bool branch; if (__builtin_types_compatible_p(typeof(*&mds_idle_clear), struct static_key_true)) branch = !arch_static_branch(&(&mds_idle_clear)->key, true); else if (__builtin_types_compatible_p(typeof(*&mds_idle_clear), struct static_key_false)) branch = !arch_static_branch_jump(&(&mds_idle_clear)->key, true); else branch = ____wrong_branch_error(); __builtin_expect(!!(branch), 1); }))
  mds_clear_cpu_buffers();
}
# 10 "./arch/x86/include/asm/irqflags.h" 2






extern inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long native_save_fl(void);
extern inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long native_save_fl(void)
{
 unsigned long flags;






 asm volatile("# __raw_save_flags\n\t"
       "pushf ; pop %0"
       : "=rm" (flags)
       :
       : "memory");

 return flags;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void native_irq_disable(void)
{
 asm volatile("cli": : :"memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void native_irq_enable(void)
{
 asm volatile("sti": : :"memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void native_safe_halt(void)
{
 mds_idle_clear_cpu_buffers();
 asm volatile("sti; hlt": : :"memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void native_halt(void)
{
 mds_idle_clear_cpu_buffers();
 asm volatile("hlt": : :"memory");
}
# 65 "./arch/x86/include/asm/irqflags.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long arch_local_save_flags(void)
{
 return native_save_fl();
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void arch_local_irq_disable(void)
{
 native_irq_disable();
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void arch_local_irq_enable(void)
{
 native_irq_enable();
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void arch_safe_halt(void)
{
 native_safe_halt();
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void halt(void)
{
 native_halt();
}




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long arch_local_irq_save(void)
{
 unsigned long flags = arch_local_save_flags();
 arch_local_irq_disable();
 return flags;
}
# 120 "./arch/x86/include/asm/irqflags.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) int arch_irqs_disabled_flags(unsigned long flags)
{
 return !(flags & (((1UL)) << (9)));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) int arch_irqs_disabled(void)
{
 unsigned long flags = arch_local_save_flags();

 return arch_irqs_disabled_flags(flags);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void arch_local_irq_restore(unsigned long flags)
{
 if (!arch_irqs_disabled_flags(flags))
  arch_local_irq_enable();
}
# 19 "./include/linux/irqflags.h" 2
# 29 "./include/linux/irqflags.h"
  static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void lockdep_softirqs_on(unsigned long ip) { }
  static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void lockdep_softirqs_off(unsigned long ip) { }
  static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void lockdep_hardirqs_on_prepare(void) { }
  static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void lockdep_hardirqs_on(unsigned long ip) { }
  static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void lockdep_hardirqs_off(unsigned long ip) { }
# 259 "./include/linux/irqflags.h"
typedef struct { void *lock; ; } class_irq_t; static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void class_irq_destructor(class_irq_t *_T) { if (_T->lock) { do { arch_local_irq_enable(); } while (0); } } static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void *class_irq_lock_ptr(class_irq_t *_T) { return _T->lock; } static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) class_irq_t class_irq_constructor(void) { class_irq_t _t = { .lock = (void*)1 }, *_T __attribute__((__unused__)) = &_t; do { arch_local_irq_disable(); } while (0); return _t; }
typedef struct { void *lock; unsigned long flags; } class_irqsave_t; static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void class_irqsave_destructor(class_irqsave_t *_T) { if (_T->lock) { do { do { ({ unsigned long __dummy; typeof(_T->flags) __dummy2; (void)(&__dummy == &__dummy2); 1; }); do { } while (0); arch_local_irq_restore(_T->flags); } while (0); } while (0); } } static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void *class_irqsave_lock_ptr(class_irqsave_t *_T) { return _T->lock; } static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) class_irqsave_t class_irqsave_constructor(void) { class_irqsave_t _t = { .lock = (void*)1 }, *_T __attribute__((__unused__)) = &_t; do { do { ({ unsigned long __dummy; typeof(_T->flags) __dummy2; (void)(&__dummy == &__dummy2); 1; }); _T->flags = arch_local_irq_save(); } while (0); } while (0); return _t; }
# 27 "./include/linux/rcupdate.h" 2
# 1 "./include/linux/preempt.h" 1
# 79 "./include/linux/preempt.h"
# 1 "./arch/x86/include/asm/preempt.h" 1
# 9 "./arch/x86/include/asm/preempt.h"
# 1 "./include/linux/static_call_types.h" 1
# 32 "./include/linux/static_call_types.h"
struct static_call_site {
 s32 addr;
 s32 key;
};
# 61 "./include/linux/static_call_types.h"
struct static_call_key {
 void *func;
 union {

  unsigned long type;
  struct static_call_mod *mods;
  struct static_call_site *sites;
 };
};
# 10 "./arch/x86/include/asm/preempt.h" 2
# 24 "./arch/x86/include/asm/preempt.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) int preempt_count(void)
{
 return ({ u32 pfo_val__; asm ("mov" "l " "%%""gs"":" "%" "[var]" ", " "%[val]" : [val] "=" "r" (pfo_val__) : [var] "m" (pcpu_hot.preempt_count)); (typeof(pcpu_hot.preempt_count))(unsigned long) pfo_val__; }) & ~0x80000000;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void preempt_count_set(int pc)
{
 int old, new;

 old = ({ u32 pfo_val__; asm ("mov" "l " "%%""gs"":" "%" "[var]" ", " "%[val]" : [val] "=" "r" (pfo_val__) : [var] "m" (pcpu_hot.preempt_count)); (typeof(pcpu_hot.preempt_count))(unsigned long) pfo_val__; });
 do {
  new = (old & 0x80000000) |
   (pc & ~0x80000000);
 } while (!({ bool success; u32 *pco_oval__ = (u32 *)(&old); u32 pco_old__ = *pco_oval__; u32 pco_new__ = ((u32)(((unsigned long) new) & 0xffffffff)); asm ("cmpxchg" "l " "%[nval]" ", " "%%""gs"":" "%" "[var]" "\n\t/* output condition code " "z" "*/\n" : "=@cc" "z" (success), [oval] "+a" (pco_old__), [var] "+m" (pcpu_hot.preempt_count) : [nval] "r" (pco_new__) : "memory"); if (__builtin_expect(!!(!success), 0)) *pco_oval__ = pco_old__; __builtin_expect(!!(success), 1); }));
}
# 58 "./arch/x86/include/asm/preempt.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void set_preempt_need_resched(void)
{
 do { u32 pto_val__ = ((u32)(((unsigned long) ~0x80000000) & 0xffffffff)); if (0) { typeof((pcpu_hot.preempt_count)) pto_tmp__; pto_tmp__ = (~0x80000000); (void)pto_tmp__; } asm ("and" "l " "%[val]" ", " "%%""gs"":" "%" "[var]" : [var] "+m" ((pcpu_hot.preempt_count)) : [val] "ri" (pto_val__)); } while (0);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void clear_preempt_need_resched(void)
{
 do { u32 pto_val__ = ((u32)(((unsigned long) 0x80000000) & 0xffffffff)); if (0) { typeof((pcpu_hot.preempt_count)) pto_tmp__; pto_tmp__ = (0x80000000); (void)pto_tmp__; } asm ("or" "l " "%[val]" ", " "%%""gs"":" "%" "[var]" : [var] "+m" ((pcpu_hot.preempt_count)) : [val] "ri" (pto_val__)); } while (0);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool test_preempt_need_resched(void)
{
 return !(({ u32 pfo_val__; asm ("mov" "l " "%%""gs"":" "%" "[var]" ", " "%[val]" : [val] "=" "r" (pfo_val__) : [var] "m" (pcpu_hot.preempt_count)); (typeof(pcpu_hot.preempt_count))(unsigned long) pfo_val__; }) & 0x80000000);
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void __preempt_count_add(int val)
{
 do { const int pao_ID__ = (__builtin_constant_p(val) && ((val) == 1 || (val) == -1)) ? (int)(val) : 0; if (0) { typeof((pcpu_hot.preempt_count)) pao_tmp__; pao_tmp__ = (val); (void)pao_tmp__; } if (pao_ID__ == 1) ({ asm ("inc" "l " "%%""gs"":" "%" "[var]" : [var] "+m" ((pcpu_hot.preempt_count))); }); else if (pao_ID__ == -1) ({ asm ("dec" "l " "%%""gs"":" "%" "[var]" : [var] "+m" ((pcpu_hot.preempt_count))); }); else do { u32 pto_val__ = ((u32)(((unsigned long) val) & 0xffffffff)); if (0) { typeof((pcpu_hot.preempt_count)) pto_tmp__; pto_tmp__ = (val); (void)pto_tmp__; } asm ("add" "l " "%[val]" ", " "%%""gs"":" "%" "[var]" : [var] "+m" ((pcpu_hot.preempt_count)) : [val] "ri" (pto_val__)); } while (0); } while (0);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void __preempt_count_sub(int val)
{
 do { const int pao_ID__ = (__builtin_constant_p(-val) && ((-val) == 1 || (-val) == -1)) ? (int)(-val) : 0; if (0) { typeof((pcpu_hot.preempt_count)) pao_tmp__; pao_tmp__ = (-val); (void)pao_tmp__; } if (pao_ID__ == 1) ({ asm ("inc" "l " "%%""gs"":" "%" "[var]" : [var] "+m" ((pcpu_hot.preempt_count))); }); else if (pao_ID__ == -1) ({ asm ("dec" "l " "%%""gs"":" "%" "[var]" : [var] "+m" ((pcpu_hot.preempt_count))); }); else do { u32 pto_val__ = ((u32)(((unsigned long) -val) & 0xffffffff)); if (0) { typeof((pcpu_hot.preempt_count)) pto_tmp__; pto_tmp__ = (-val); (void)pto_tmp__; } asm ("add" "l " "%[val]" ", " "%%""gs"":" "%" "[var]" : [var] "+m" ((pcpu_hot.preempt_count)) : [val] "ri" (pto_val__)); } while (0); } while (0);
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool __preempt_count_dec_and_test(void)
{
 return ({ bool c; asm volatile ("decl" " " "%%""gs"":" "%" "[var]" "\n\t/* output condition code " "e" "*/\n" : [var] "+m" (pcpu_hot.preempt_count), "=@cc" "e" (c) : : "memory"); c; })
                              ;
}




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool should_resched(int preempt_offset)
{
 return __builtin_expect(!!(({ u32 pfo_val__; asm ("mov" "l " "%%""gs"":" "%" "[var]" ", " "%[val]" : [val] "=" "r" (pfo_val__) : [var] "m" (pcpu_hot.preempt_count)); (typeof(pcpu_hot.preempt_count))(unsigned long) pfo_val__; }) == preempt_offset), 0);
}



extern void preempt_schedule(void);
extern void preempt_schedule_thunk(void);




extern void preempt_schedule_notrace(void);
extern void preempt_schedule_notrace_thunk(void);






extern struct static_call_key __SCK__preempt_schedule; extern typeof(preempt_schedule_thunk) __SCT__preempt_schedule;;







extern struct static_call_key __SCK__preempt_schedule_notrace; extern typeof(preempt_schedule_notrace_thunk) __SCT__preempt_schedule_notrace;;
# 80 "./include/linux/preempt.h" 2
# 90 "./include/linux/preempt.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned char interrupt_context_level(void)
{
 unsigned long pc = preempt_count();
 unsigned char level = 0;

 level += !!(pc & ((((1UL << (4))-1) << (((0 + 8) + 8) + 4))));
 level += !!(pc & ((((1UL << (4))-1) << (((0 + 8) + 8) + 4)) | (((1UL << (4))-1) << ((0 + 8) + 8))));
 level += !!(pc & ((((1UL << (4))-1) << (((0 + 8) + 8) + 4)) | (((1UL << (4))-1) << ((0 + 8) + 8)) | (1UL << (0 + 8))));

 return level;
}
# 428 "./include/linux/preempt.h"
extern void migrate_disable(void);
extern void migrate_enable(void);
# 474 "./include/linux/preempt.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void preempt_enable_nested(void)
{
 if (0)
  do { __asm__ __volatile__("": : :"memory"); if (__builtin_expect(!!(__preempt_count_dec_and_test()), 0)) do { static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable___SCK__preempt_schedule8 = (void *)&__SCK__preempt_schedule;; asm volatile ("call " "__SCT__preempt_schedule" : "+r" (current_stack_pointer)); } while (0); } while (0);
}

typedef struct { void *lock; ; } class_preempt_t; static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void class_preempt_destructor(class_preempt_t *_T) { if (_T->lock) { do { __asm__ __volatile__("": : :"memory"); if (__builtin_expect(!!(__preempt_count_dec_and_test()), 0)) do { static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable___SCK__preempt_schedule9 = (void *)&__SCK__preempt_schedule;; asm volatile ("call " "__SCT__preempt_schedule" : "+r" (current_stack_pointer)); } while (0); } while (0); } } static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void *class_preempt_lock_ptr(class_preempt_t *_T) { return _T->lock; } static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) class_preempt_t class_preempt_constructor(void) { class_preempt_t _t = { .lock = (void*)1 }, *_T __attribute__((__unused__)) = &_t; do { __preempt_count_add(1); __asm__ __volatile__("": : :"memory"); } while (0); return _t; }
typedef struct { void *lock; ; } class_preempt_notrace_t; static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void class_preempt_notrace_destructor(class_preempt_notrace_t *_T) { if (_T->lock) { do { __asm__ __volatile__("": : :"memory"); if (__builtin_expect(!!(__preempt_count_dec_and_test()), 0)) do { static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable___SCK__preempt_schedule_notrace10 = (void *)&__SCK__preempt_schedule_notrace;; asm volatile ("call " "__SCT__preempt_schedule_notrace" : "+r" (current_stack_pointer)); } while (0); } while (0); } } static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void *class_preempt_notrace_lock_ptr(class_preempt_notrace_t *_T) { return _T->lock; } static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) class_preempt_notrace_t class_preempt_notrace_constructor(void) { class_preempt_notrace_t _t = { .lock = (void*)1 }, *_T __attribute__((__unused__)) = &_t; do { __preempt_count_add(1); __asm__ __volatile__("": : :"memory"); } while (0); return _t; }
typedef struct { void *lock; ; } class_migrate_t; static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void class_migrate_destructor(class_migrate_t *_T) { if (_T->lock) { migrate_enable(); } } static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void *class_migrate_lock_ptr(class_migrate_t *_T) { return _T->lock; } static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) class_migrate_t class_migrate_constructor(void) { class_migrate_t _t = { .lock = (void*)1 }, *_T __attribute__((__unused__)) = &_t; migrate_disable(); return _t; }
# 28 "./include/linux/rcupdate.h" 2
# 1 "./include/linux/bottom_half.h" 1




# 1 "./include/linux/instruction_pointer.h" 1
# 6 "./include/linux/bottom_half.h" 2





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void __local_bh_disable_ip(unsigned long ip, unsigned int cnt)
{
 __preempt_count_add(cnt);
 __asm__ __volatile__("": : :"memory");
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void local_bh_disable(void)
{
 __local_bh_disable_ip(({ unsigned long __here; asm ("lea 0(%%rip), %0" : "=r" (__here)); __here; }), (2 * (1UL << (0 + 8))));
}

extern void _local_bh_enable(void);
extern void __local_bh_enable_ip(unsigned long ip, unsigned int cnt);

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void local_bh_enable_ip(unsigned long ip)
{
 __local_bh_enable_ip(ip, (2 * (1UL << (0 + 8))));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void local_bh_enable(void)
{
 __local_bh_enable_ip(({ unsigned long __here; asm ("lea 0(%%rip), %0" : "=r" (__here)); __here; }), (2 * (1UL << (0 + 8))));
}




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool local_bh_blocked(void) { return false; }
# 29 "./include/linux/rcupdate.h" 2
# 1 "./include/linux/lockdep.h" 1
# 13 "./include/linux/lockdep.h"
# 1 "./include/linux/lockdep_types.h" 1
# 17 "./include/linux/lockdep_types.h"
enum lockdep_wait_type {
 LD_WAIT_INV = 0,

 LD_WAIT_FREE,
 LD_WAIT_SPIN,




 LD_WAIT_CONFIG = LD_WAIT_SPIN,

 LD_WAIT_SLEEP,

 LD_WAIT_MAX,
};

enum lockdep_lock_type {
 LD_LOCK_NORMAL = 0,
 LD_LOCK_PERCPU,
 LD_LOCK_WAIT_OVERRIDE,
 LD_LOCK_MAX,
};
# 263 "./include/linux/lockdep_types.h"
struct lock_class_key { };




struct lockdep_map { };

struct pin_cookie { };
# 14 "./include/linux/lockdep.h" 2
# 1 "./include/linux/smp.h" 1
# 10 "./include/linux/smp.h"
# 1 "./include/linux/errno.h" 1




# 1 "./include/uapi/linux/errno.h" 1
# 1 "./arch/x86/include/generated/uapi/asm/errno.h" 1
# 1 "./include/uapi/asm-generic/errno.h" 1




# 1 "./include/uapi/asm-generic/errno-base.h" 1
# 6 "./include/uapi/asm-generic/errno.h" 2
# 2 "./arch/x86/include/generated/uapi/asm/errno.h" 2
# 2 "./include/uapi/linux/errno.h" 2
# 6 "./include/linux/errno.h" 2
# 11 "./include/linux/smp.h" 2

# 1 "./include/linux/list.h" 1







# 1 "./include/linux/poison.h" 1
# 9 "./include/linux/list.h" 2
# 35 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void INIT_LIST_HEAD(struct list_head *list)
{
 do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_11(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(list->next) == sizeof(char) || sizeof(list->next) == sizeof(short) || sizeof(list->next) == sizeof(int) || sizeof(list->next) == sizeof(long)) || sizeof(list->next) == sizeof(long long))) __compiletime_assert_11(); } while (0); do { *(volatile typeof(list->next) *)&(list->next) = (list); } while (0); } while (0);
 do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_12(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(list->prev) == sizeof(char) || sizeof(list->prev) == sizeof(short) || sizeof(list->prev) == sizeof(int) || sizeof(list->prev) == sizeof(long)) || sizeof(list->prev) == sizeof(long long))) __compiletime_assert_12(); } while (0); do { *(volatile typeof(list->prev) *)&(list->prev) = (list); } while (0); } while (0);
}
# 128 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool __list_add_valid(struct list_head *new,
    struct list_head *prev,
    struct list_head *next)
{
 return true;
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool __list_del_entry_valid(struct list_head *entry)
{
 return true;
}
# 146 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __list_add(struct list_head *new,
         struct list_head *prev,
         struct list_head *next)
{
 if (!__list_add_valid(new, prev, next))
  return;

 next->prev = new;
 new->next = next;
 new->prev = prev;
 do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_13(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(prev->next) == sizeof(char) || sizeof(prev->next) == sizeof(short) || sizeof(prev->next) == sizeof(int) || sizeof(prev->next) == sizeof(long)) || sizeof(prev->next) == sizeof(long long))) __compiletime_assert_13(); } while (0); do { *(volatile typeof(prev->next) *)&(prev->next) = (new); } while (0); } while (0);
}
# 167 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_add(struct list_head *new, struct list_head *head)
{
 __list_add(new, head, head->next);
}
# 181 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_add_tail(struct list_head *new, struct list_head *head)
{
 __list_add(new, head->prev, head);
}
# 193 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __list_del(struct list_head * prev, struct list_head * next)
{
 next->prev = prev;
 do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_14(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(prev->next) == sizeof(char) || sizeof(prev->next) == sizeof(short) || sizeof(prev->next) == sizeof(int) || sizeof(prev->next) == sizeof(long)) || sizeof(prev->next) == sizeof(long long))) __compiletime_assert_14(); } while (0); do { *(volatile typeof(prev->next) *)&(prev->next) = (next); } while (0); } while (0);
}
# 207 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __list_del_clearprev(struct list_head *entry)
{
 __list_del(entry->prev, entry->next);
 entry->prev = ((void *)0);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __list_del_entry(struct list_head *entry)
{
 if (!__list_del_entry_valid(entry))
  return;

 __list_del(entry->prev, entry->next);
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_del(struct list_head *entry)
{
 __list_del_entry(entry);
 entry->next = ((void *) 0x100 + (0xdead000000000000UL));
 entry->prev = ((void *) 0x122 + (0xdead000000000000UL));
}
# 241 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_replace(struct list_head *old,
    struct list_head *new)
{
 new->next = old->next;
 new->next->prev = new;
 new->prev = old->prev;
 new->prev->next = new;
}
# 257 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_replace_init(struct list_head *old,
         struct list_head *new)
{
 list_replace(old, new);
 INIT_LIST_HEAD(old);
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_swap(struct list_head *entry1,
        struct list_head *entry2)
{
 struct list_head *pos = entry2->prev;

 list_del(entry2);
 list_replace(entry1, entry2);
 if (pos == entry1)
  pos = entry2;
 list_add(entry1, pos);
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_del_init(struct list_head *entry)
{
 __list_del_entry(entry);
 INIT_LIST_HEAD(entry);
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_move(struct list_head *list, struct list_head *head)
{
 __list_del_entry(list);
 list_add(list, head);
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_move_tail(struct list_head *list,
      struct list_head *head)
{
 __list_del_entry(list);
 list_add_tail(list, head);
}
# 323 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_bulk_move_tail(struct list_head *head,
           struct list_head *first,
           struct list_head *last)
{
 first->prev->next = last->next;
 last->next->prev = first->prev;

 head->prev->next = first;
 first->prev = head->prev;

 last->next = head;
 head->prev = last;
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int list_is_first(const struct list_head *list, const struct list_head *head)
{
 return list->prev == head;
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int list_is_last(const struct list_head *list, const struct list_head *head)
{
 return list->next == head;
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int list_is_head(const struct list_head *list, const struct list_head *head)
{
 return list == head;
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int list_empty(const struct list_head *head)
{
 return ({ do { __attribute__((__noreturn__)) extern void __compiletime_assert_15(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(head->next) == sizeof(char) || sizeof(head->next) == sizeof(short) || sizeof(head->next) == sizeof(int) || sizeof(head->next) == sizeof(long)) || sizeof(head->next) == sizeof(long long))) __compiletime_assert_15(); } while (0); (*(const volatile typeof( _Generic((head->next), char: (char)0, unsigned char: (unsigned char)0, signed char: (signed char)0, unsigned short: (unsigned short)0, signed short: (signed short)0, unsigned int: (unsigned int)0, signed int: (signed int)0, unsigned long: (unsigned long)0, signed long: (signed long)0, unsigned long long: (unsigned long long)0, signed long long: (signed long long)0, default: (head->next))) *)&(head->next)); }) == head;
}
# 387 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_del_init_careful(struct list_head *entry)
{
 __list_del_entry(entry);
 do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_16(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(entry->prev) == sizeof(char) || sizeof(entry->prev) == sizeof(short) || sizeof(entry->prev) == sizeof(int) || sizeof(entry->prev) == sizeof(long)) || sizeof(entry->prev) == sizeof(long long))) __compiletime_assert_16(); } while (0); do { *(volatile typeof(entry->prev) *)&(entry->prev) = (entry); } while (0); } while (0);
 do { do { } while (0); do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_17(void) __attribute__((__error__("Need native word sized stores/loads for atomicity."))); if (!((sizeof(*&entry->next) == sizeof(char) || sizeof(*&entry->next) == sizeof(short) || sizeof(*&entry->next) == sizeof(int) || sizeof(*&entry->next) == sizeof(long)))) __compiletime_assert_17(); } while (0); __asm__ __volatile__("": : :"memory"); do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_18(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(*&entry->next) == sizeof(char) || sizeof(*&entry->next) == sizeof(short) || sizeof(*&entry->next) == sizeof(int) || sizeof(*&entry->next) == sizeof(long)) || sizeof(*&entry->next) == sizeof(long long))) __compiletime_assert_18(); } while (0); do { *(volatile typeof(*&entry->next) *)&(*&entry->next) = (entry); } while (0); } while (0); } while (0); } while (0);
}
# 407 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int list_empty_careful(const struct list_head *head)
{
 struct list_head *next = ({ typeof(*&head->next) ___p1 = ({ do { __attribute__((__noreturn__)) extern void __compiletime_assert_19(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(*&head->next) == sizeof(char) || sizeof(*&head->next) == sizeof(short) || sizeof(*&head->next) == sizeof(int) || sizeof(*&head->next) == sizeof(long)) || sizeof(*&head->next) == sizeof(long long))) __compiletime_assert_19(); } while (0); (*(const volatile typeof( _Generic((*&head->next), char: (char)0, unsigned char: (unsigned char)0, signed char: (signed char)0, unsigned short: (unsigned short)0, signed short: (signed short)0, unsigned int: (unsigned int)0, signed int: (signed int)0, unsigned long: (unsigned long)0, signed long: (signed long)0, unsigned long long: (unsigned long long)0, signed long long: (signed long long)0, default: (*&head->next))) *)&(*&head->next)); }); do { __attribute__((__noreturn__)) extern void __compiletime_assert_20(void) __attribute__((__error__("Need native word sized stores/loads for atomicity."))); if (!((sizeof(*&head->next) == sizeof(char) || sizeof(*&head->next) == sizeof(short) || sizeof(*&head->next) == sizeof(int) || sizeof(*&head->next) == sizeof(long)))) __compiletime_assert_20(); } while (0); __asm__ __volatile__("": : :"memory"); ___p1; });
 return list_is_head(next, head) && (next == ({ do { __attribute__((__noreturn__)) extern void __compiletime_assert_21(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(head->prev) == sizeof(char) || sizeof(head->prev) == sizeof(short) || sizeof(head->prev) == sizeof(int) || sizeof(head->prev) == sizeof(long)) || sizeof(head->prev) == sizeof(long long))) __compiletime_assert_21(); } while (0); (*(const volatile typeof( _Generic((head->prev), char: (char)0, unsigned char: (unsigned char)0, signed char: (signed char)0, unsigned short: (unsigned short)0, signed short: (signed short)0, unsigned int: (unsigned int)0, signed int: (signed int)0, unsigned long: (unsigned long)0, signed long: (signed long)0, unsigned long long: (unsigned long long)0, signed long long: (signed long long)0, default: (head->prev))) *)&(head->prev)); }));
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_rotate_left(struct list_head *head)
{
 struct list_head *first;

 if (!list_empty(head)) {
  first = head->next;
  list_move_tail(first, head);
 }
}
# 434 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_rotate_to_front(struct list_head *list,
     struct list_head *head)
{





 list_move_tail(head, list);
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int list_is_singular(const struct list_head *head)
{
 return !list_empty(head) && (head->next == head->prev);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __list_cut_position(struct list_head *list,
  struct list_head *head, struct list_head *entry)
{
 struct list_head *new_first = entry->next;
 list->next = head->next;
 list->next->prev = list;
 list->prev = entry;
 entry->next = list;
 head->next = new_first;
 new_first->prev = head;
}
# 480 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_cut_position(struct list_head *list,
  struct list_head *head, struct list_head *entry)
{
 if (list_empty(head))
  return;
 if (list_is_singular(head) && !list_is_head(entry, head) && (entry != head->next))
  return;
 if (list_is_head(entry, head))
  INIT_LIST_HEAD(list);
 else
  __list_cut_position(list, head, entry);
}
# 507 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_cut_before(struct list_head *list,
       struct list_head *head,
       struct list_head *entry)
{
 if (head->next == entry) {
  INIT_LIST_HEAD(list);
  return;
 }
 list->next = head->next;
 list->next->prev = list;
 list->prev = entry->prev;
 list->prev->next = list;
 head->next = entry;
 entry->prev = head;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __list_splice(const struct list_head *list,
     struct list_head *prev,
     struct list_head *next)
{
 struct list_head *first = list->next;
 struct list_head *last = list->prev;

 first->prev = prev;
 prev->next = first;

 last->next = next;
 next->prev = last;
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_splice(const struct list_head *list,
    struct list_head *head)
{
 if (!list_empty(list))
  __list_splice(list, head, head->next);
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_splice_tail(struct list_head *list,
    struct list_head *head)
{
 if (!list_empty(list))
  __list_splice(list, head->prev, head);
}
# 568 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_splice_init(struct list_head *list,
        struct list_head *head)
{
 if (!list_empty(list)) {
  __list_splice(list, head, head->next);
  INIT_LIST_HEAD(list);
 }
}
# 585 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void list_splice_tail_init(struct list_head *list,
      struct list_head *head)
{
 if (!list_empty(list)) {
  __list_splice(list, head->prev, head);
  INIT_LIST_HEAD(list);
 }
}
# 751 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) size_t list_count_nodes(struct list_head *head)
{
 struct list_head *pos;
 size_t count = 0;

 for (pos = (head)->next; !list_is_head(pos, (head)); pos = pos->next)
  count++;

 return count;
}
# 942 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void INIT_HLIST_NODE(struct hlist_node *h)
{
 h->next = ((void *)0);
 h->pprev = ((void *)0);
}
# 956 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int hlist_unhashed(const struct hlist_node *h)
{
 return !h->pprev;
}
# 969 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int hlist_unhashed_lockless(const struct hlist_node *h)
{
 return !({ do { __attribute__((__noreturn__)) extern void __compiletime_assert_22(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(h->pprev) == sizeof(char) || sizeof(h->pprev) == sizeof(short) || sizeof(h->pprev) == sizeof(int) || sizeof(h->pprev) == sizeof(long)) || sizeof(h->pprev) == sizeof(long long))) __compiletime_assert_22(); } while (0); (*(const volatile typeof( _Generic((h->pprev), char: (char)0, unsigned char: (unsigned char)0, signed char: (signed char)0, unsigned short: (unsigned short)0, signed short: (signed short)0, unsigned int: (unsigned int)0, signed int: (signed int)0, unsigned long: (unsigned long)0, signed long: (signed long)0, unsigned long long: (unsigned long long)0, signed long long: (signed long long)0, default: (h->pprev))) *)&(h->pprev)); });
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int hlist_empty(const struct hlist_head *h)
{
 return !({ do { __attribute__((__noreturn__)) extern void __compiletime_assert_23(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(h->first) == sizeof(char) || sizeof(h->first) == sizeof(short) || sizeof(h->first) == sizeof(int) || sizeof(h->first) == sizeof(long)) || sizeof(h->first) == sizeof(long long))) __compiletime_assert_23(); } while (0); (*(const volatile typeof( _Generic((h->first), char: (char)0, unsigned char: (unsigned char)0, signed char: (signed char)0, unsigned short: (unsigned short)0, signed short: (signed short)0, unsigned int: (unsigned int)0, signed int: (signed int)0, unsigned long: (unsigned long)0, signed long: (signed long)0, unsigned long long: (unsigned long long)0, signed long long: (signed long long)0, default: (h->first))) *)&(h->first)); });
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __hlist_del(struct hlist_node *n)
{
 struct hlist_node *next = n->next;
 struct hlist_node **pprev = n->pprev;

 do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_24(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(*pprev) == sizeof(char) || sizeof(*pprev) == sizeof(short) || sizeof(*pprev) == sizeof(int) || sizeof(*pprev) == sizeof(long)) || sizeof(*pprev) == sizeof(long long))) __compiletime_assert_24(); } while (0); do { *(volatile typeof(*pprev) *)&(*pprev) = (next); } while (0); } while (0);
 if (next)
  do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_25(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(next->pprev) == sizeof(char) || sizeof(next->pprev) == sizeof(short) || sizeof(next->pprev) == sizeof(int) || sizeof(next->pprev) == sizeof(long)) || sizeof(next->pprev) == sizeof(long long))) __compiletime_assert_25(); } while (0); do { *(volatile typeof(next->pprev) *)&(next->pprev) = (pprev); } while (0); } while (0);
}
# 1000 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void hlist_del(struct hlist_node *n)
{
 __hlist_del(n);
 n->next = ((void *) 0x100 + (0xdead000000000000UL));
 n->pprev = ((void *) 0x122 + (0xdead000000000000UL));
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void hlist_del_init(struct hlist_node *n)
{
 if (!hlist_unhashed(n)) {
  __hlist_del(n);
  INIT_HLIST_NODE(n);
 }
}
# 1029 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void hlist_add_head(struct hlist_node *n, struct hlist_head *h)
{
 struct hlist_node *first = h->first;
 do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_26(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(n->next) == sizeof(char) || sizeof(n->next) == sizeof(short) || sizeof(n->next) == sizeof(int) || sizeof(n->next) == sizeof(long)) || sizeof(n->next) == sizeof(long long))) __compiletime_assert_26(); } while (0); do { *(volatile typeof(n->next) *)&(n->next) = (first); } while (0); } while (0);
 if (first)
  do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_27(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(first->pprev) == sizeof(char) || sizeof(first->pprev) == sizeof(short) || sizeof(first->pprev) == sizeof(int) || sizeof(first->pprev) == sizeof(long)) || sizeof(first->pprev) == sizeof(long long))) __compiletime_assert_27(); } while (0); do { *(volatile typeof(first->pprev) *)&(first->pprev) = (&n->next); } while (0); } while (0);
 do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_28(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(h->first) == sizeof(char) || sizeof(h->first) == sizeof(short) || sizeof(h->first) == sizeof(int) || sizeof(h->first) == sizeof(long)) || sizeof(h->first) == sizeof(long long))) __compiletime_assert_28(); } while (0); do { *(volatile typeof(h->first) *)&(h->first) = (n); } while (0); } while (0);
 do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_29(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(n->pprev) == sizeof(char) || sizeof(n->pprev) == sizeof(short) || sizeof(n->pprev) == sizeof(int) || sizeof(n->pprev) == sizeof(long)) || sizeof(n->pprev) == sizeof(long long))) __compiletime_assert_29(); } while (0); do { *(volatile typeof(n->pprev) *)&(n->pprev) = (&h->first); } while (0); } while (0);
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void hlist_add_before(struct hlist_node *n,
        struct hlist_node *next)
{
 do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_30(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(n->pprev) == sizeof(char) || sizeof(n->pprev) == sizeof(short) || sizeof(n->pprev) == sizeof(int) || sizeof(n->pprev) == sizeof(long)) || sizeof(n->pprev) == sizeof(long long))) __compiletime_assert_30(); } while (0); do { *(volatile typeof(n->pprev) *)&(n->pprev) = (next->pprev); } while (0); } while (0);
 do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_31(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(n->next) == sizeof(char) || sizeof(n->next) == sizeof(short) || sizeof(n->next) == sizeof(int) || sizeof(n->next) == sizeof(long)) || sizeof(n->next) == sizeof(long long))) __compiletime_assert_31(); } while (0); do { *(volatile typeof(n->next) *)&(n->next) = (next); } while (0); } while (0);
 do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_32(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(next->pprev) == sizeof(char) || sizeof(next->pprev) == sizeof(short) || sizeof(next->pprev) == sizeof(int) || sizeof(next->pprev) == sizeof(long)) || sizeof(next->pprev) == sizeof(long long))) __compiletime_assert_32(); } while (0); do { *(volatile typeof(next->pprev) *)&(next->pprev) = (&n->next); } while (0); } while (0);
 do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_33(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(*(n->pprev)) == sizeof(char) || sizeof(*(n->pprev)) == sizeof(short) || sizeof(*(n->pprev)) == sizeof(int) || sizeof(*(n->pprev)) == sizeof(long)) || sizeof(*(n->pprev)) == sizeof(long long))) __compiletime_assert_33(); } while (0); do { *(volatile typeof(*(n->pprev)) *)&(*(n->pprev)) = (n); } while (0); } while (0);
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void hlist_add_behind(struct hlist_node *n,
        struct hlist_node *prev)
{
 do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_34(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(n->next) == sizeof(char) || sizeof(n->next) == sizeof(short) || sizeof(n->next) == sizeof(int) || sizeof(n->next) == sizeof(long)) || sizeof(n->next) == sizeof(long long))) __compiletime_assert_34(); } while (0); do { *(volatile typeof(n->next) *)&(n->next) = (prev->next); } while (0); } while (0);
 do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_35(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(prev->next) == sizeof(char) || sizeof(prev->next) == sizeof(short) || sizeof(prev->next) == sizeof(int) || sizeof(prev->next) == sizeof(long)) || sizeof(prev->next) == sizeof(long long))) __compiletime_assert_35(); } while (0); do { *(volatile typeof(prev->next) *)&(prev->next) = (n); } while (0); } while (0);
 do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_36(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(n->pprev) == sizeof(char) || sizeof(n->pprev) == sizeof(short) || sizeof(n->pprev) == sizeof(int) || sizeof(n->pprev) == sizeof(long)) || sizeof(n->pprev) == sizeof(long long))) __compiletime_assert_36(); } while (0); do { *(volatile typeof(n->pprev) *)&(n->pprev) = (&prev->next); } while (0); } while (0);

 if (n->next)
  do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_37(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(n->next->pprev) == sizeof(char) || sizeof(n->next->pprev) == sizeof(short) || sizeof(n->next->pprev) == sizeof(int) || sizeof(n->next->pprev) == sizeof(long)) || sizeof(n->next->pprev) == sizeof(long long))) __compiletime_assert_37(); } while (0); do { *(volatile typeof(n->next->pprev) *)&(n->next->pprev) = (&n->next); } while (0); } while (0);
}
# 1077 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void hlist_add_fake(struct hlist_node *n)
{
 n->pprev = &n->next;
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool hlist_fake(struct hlist_node *h)
{
 return h->pprev == &h->next;
}
# 1099 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool
hlist_is_singular_node(struct hlist_node *n, struct hlist_head *h)
{
 return !n->next && n->pprev == &h->first;
}
# 1113 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void hlist_move_list(struct hlist_head *old,
       struct hlist_head *new)
{
 new->first = old->first;
 if (new->first)
  new->first->pprev = &new->first;
 old->first = ((void *)0);
}
# 1130 "./include/linux/list.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void hlist_splice_init(struct hlist_head *from,
         struct hlist_node *last,
         struct hlist_head *to)
{
 if (to->first)
  to->first->pprev = &last->next;
 last->next = to->first;
 to->first = from->first;
 from->first->pprev = &to->first;
 from->first = ((void *)0);
}
# 13 "./include/linux/smp.h" 2
# 1 "./include/linux/cpumask.h" 1
# 10 "./include/linux/cpumask.h"
# 1 "./include/linux/kernel.h" 1
# 14 "./include/linux/kernel.h"
# 1 "./include/linux/stdarg.h" 1




typedef __builtin_va_list va_list;
# 15 "./include/linux/kernel.h" 2
# 1 "./include/linux/align.h" 1
# 16 "./include/linux/kernel.h" 2
# 1 "./include/linux/array_size.h" 1
# 17 "./include/linux/kernel.h" 2
# 1 "./include/linux/limits.h" 1




# 1 "./include/uapi/linux/limits.h" 1
# 6 "./include/linux/limits.h" 2

# 1 "./include/vdso/limits.h" 1
# 8 "./include/linux/limits.h" 2
# 18 "./include/linux/kernel.h" 2





# 1 "./include/linux/bitops.h" 1




# 1 "./arch/x86/include/generated/uapi/asm/types.h" 1
# 6 "./include/linux/bitops.h" 2
# 24 "./include/linux/bitops.h"
extern unsigned int __sw_hweight8(unsigned int w);
extern unsigned int __sw_hweight16(unsigned int w);
extern unsigned int __sw_hweight32(unsigned int w);
extern unsigned long __sw_hweight64(__u64 w);






# 1 "./include/asm-generic/bitops/generic-non-atomic.h" 1
# 27 "./include/asm-generic/bitops/generic-non-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
generic___set_bit(unsigned long nr, volatile unsigned long *addr)
{
 unsigned long mask = ((((1UL))) << ((nr) % 64));
 unsigned long *p = ((unsigned long *)addr) + ((nr) / 64);

 *p |= mask;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
generic___clear_bit(unsigned long nr, volatile unsigned long *addr)
{
 unsigned long mask = ((((1UL))) << ((nr) % 64));
 unsigned long *p = ((unsigned long *)addr) + ((nr) / 64);

 *p &= ~mask;
}
# 54 "./include/asm-generic/bitops/generic-non-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
generic___change_bit(unsigned long nr, volatile unsigned long *addr)
{
 unsigned long mask = ((((1UL))) << ((nr) % 64));
 unsigned long *p = ((unsigned long *)addr) + ((nr) / 64);

 *p ^= mask;
}
# 72 "./include/asm-generic/bitops/generic-non-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
generic___test_and_set_bit(unsigned long nr, volatile unsigned long *addr)
{
 unsigned long mask = ((((1UL))) << ((nr) % 64));
 unsigned long *p = ((unsigned long *)addr) + ((nr) / 64);
 unsigned long old = *p;

 *p = old | mask;
 return (old & mask) != 0;
}
# 92 "./include/asm-generic/bitops/generic-non-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
generic___test_and_clear_bit(unsigned long nr, volatile unsigned long *addr)
{
 unsigned long mask = ((((1UL))) << ((nr) % 64));
 unsigned long *p = ((unsigned long *)addr) + ((nr) / 64);
 unsigned long old = *p;

 *p = old & ~mask;
 return (old & mask) != 0;
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
generic___test_and_change_bit(unsigned long nr, volatile unsigned long *addr)
{
 unsigned long mask = ((((1UL))) << ((nr) % 64));
 unsigned long *p = ((unsigned long *)addr) + ((nr) / 64);
 unsigned long old = *p;

 *p = old ^ mask;
 return (old & mask) != 0;
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
generic_test_bit(unsigned long nr, const volatile unsigned long *addr)
{





 return 1UL & (addr[((nr) / 64)] >> (nr & (64 -1)));
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
generic_test_bit_acquire(unsigned long nr, const volatile unsigned long *addr)
{
 unsigned long *p = ((unsigned long *)addr) + ((nr) / 64);
 return 1UL & (({ typeof(*p) ___p1 = ({ do { __attribute__((__noreturn__)) extern void __compiletime_assert_38(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(*p) == sizeof(char) || sizeof(*p) == sizeof(short) || sizeof(*p) == sizeof(int) || sizeof(*p) == sizeof(long)) || sizeof(*p) == sizeof(long long))) __compiletime_assert_38(); } while (0); (*(const volatile typeof( _Generic((*p), char: (char)0, unsigned char: (unsigned char)0, signed char: (signed char)0, unsigned short: (unsigned short)0, signed short: (signed short)0, unsigned int: (unsigned int)0, signed int: (signed int)0, unsigned long: (unsigned long)0, signed long: (signed long)0, unsigned long long: (unsigned long long)0, signed long long: (signed long long)0, default: (*p))) *)&(*p)); }); do { __attribute__((__noreturn__)) extern void __compiletime_assert_39(void) __attribute__((__error__("Need native word sized stores/loads for atomicity."))); if (!((sizeof(*p) == sizeof(char) || sizeof(*p) == sizeof(short) || sizeof(*p) == sizeof(int) || sizeof(*p) == sizeof(long)))) __compiletime_assert_39(); } while (0); __asm__ __volatile__("": : :"memory"); ___p1; }) >> (nr & (64 -1)));
}
# 165 "./include/asm-generic/bitops/generic-non-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
const_test_bit(unsigned long nr, const volatile unsigned long *addr)
{
 const unsigned long *p = (const unsigned long *)addr + ((nr) / 64);
 unsigned long mask = ((((1UL))) << ((nr) % 64));
 unsigned long val = *p;

 return !!(val & mask);
}
# 35 "./include/linux/bitops.h" 2
# 68 "./include/linux/bitops.h"
# 1 "./arch/x86/include/asm/bitops.h" 1
# 51 "./arch/x86/include/asm/bitops.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
arch_set_bit(long nr, volatile unsigned long *addr)
{
 if (__builtin_constant_p(nr)) {
  asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "orb %b1,%0"
   : "+m" (*(volatile char *) ((void *)(addr) + ((nr)>>3)))
   : "iq" ((1 << ((nr) & 7)))
   : "memory");
 } else {
  asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " " " "btsq" " " " %1,%0"
   : : "m" (*(volatile long *) (addr)), "Ir" (nr) : "memory");
 }
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
arch___set_bit(unsigned long nr, volatile unsigned long *addr)
{
 asm volatile(" " "btsq" " " " %1,%0" : : "m" (*(volatile long *) (addr)), "Ir" (nr) : "memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
arch_clear_bit(long nr, volatile unsigned long *addr)
{
 if (__builtin_constant_p(nr)) {
  asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "andb %b1,%0"
   : "+m" (*(volatile char *) ((void *)(addr) + ((nr)>>3)))
   : "iq" (~(1 << ((nr) & 7))));
 } else {
  asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " " " "btrq" " " " %1,%0"
   : : "m" (*(volatile long *) (addr)), "Ir" (nr) : "memory");
 }
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
arch_clear_bit_unlock(long nr, volatile unsigned long *addr)
{
 __asm__ __volatile__("": : :"memory");
 arch_clear_bit(nr, addr);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
arch___clear_bit(unsigned long nr, volatile unsigned long *addr)
{
 asm volatile(" " "btrq" " " " %1,%0" : : "m" (*(volatile long *) (addr)), "Ir" (nr) : "memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool arch_xor_unlock_is_negative_byte(unsigned long mask,
  volatile unsigned long *addr)
{
 bool negative;
 asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xorb %2,%1"
  "\n\t/* output condition code " "s" "*/\n"
  : "=@cc" "s" (negative), "+m" (*(volatile char *) (addr))
  : "iq" ((char)mask) : "memory");
 return negative;
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
arch___clear_bit_unlock(long nr, volatile unsigned long *addr)
{
 arch___clear_bit(nr, addr);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
arch___change_bit(unsigned long nr, volatile unsigned long *addr)
{
 asm volatile(" " "btcq" " " " %1,%0" : : "m" (*(volatile long *) (addr)), "Ir" (nr) : "memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
arch_change_bit(long nr, volatile unsigned long *addr)
{
 if (__builtin_constant_p(nr)) {
  asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " "xorb %b1,%0"
   : "+m" (*(volatile char *) ((void *)(addr) + ((nr)>>3)))
   : "iq" ((1 << ((nr) & 7))));
 } else {
  asm volatile(".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " " " "btcq" " " " %1,%0"
   : : "m" (*(volatile long *) (addr)), "Ir" (nr) : "memory");
 }
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
arch_test_and_set_bit(long nr, volatile unsigned long *addr)
{
 return ({ bool c; asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " " " "btsq" " " " %[val], " "%[var]" "\n\t/* output condition code " "c" "*/\n" : [var] "+m" (*addr), "=@cc" "c" (c) : [val] "Ir" (nr) : "memory"); c; });
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
arch_test_and_set_bit_lock(long nr, volatile unsigned long *addr)
{
 return arch_test_and_set_bit(nr, addr);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
arch___test_and_set_bit(unsigned long nr, volatile unsigned long *addr)
{
 bool oldbit;

 asm(" " "btsq" " " " %2,%1"
     "\n\t/* output condition code " "c" "*/\n"
     : "=@cc" "c" (oldbit)
     : "m" (*(volatile long *) (addr)), "Ir" (nr) : "memory");
 return oldbit;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
arch_test_and_clear_bit(long nr, volatile unsigned long *addr)
{
 return ({ bool c; asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " " " "btrq" " " " %[val], " "%[var]" "\n\t/* output condition code " "c" "*/\n" : [var] "+m" (*addr), "=@cc" "c" (c) : [val] "Ir" (nr) : "memory"); c; });
}
# 172 "./arch/x86/include/asm/bitops.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
arch___test_and_clear_bit(unsigned long nr, volatile unsigned long *addr)
{
 bool oldbit;

 asm volatile(" " "btrq" " " " %2,%1"
       "\n\t/* output condition code " "c" "*/\n"
       : "=@cc" "c" (oldbit)
       : "m" (*(volatile long *) (addr)), "Ir" (nr) : "memory");
 return oldbit;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
arch___test_and_change_bit(unsigned long nr, volatile unsigned long *addr)
{
 bool oldbit;

 asm volatile(" " "btcq" " " " %2,%1"
       "\n\t/* output condition code " "c" "*/\n"
       : "=@cc" "c" (oldbit)
       : "m" (*(volatile long *) (addr)), "Ir" (nr) : "memory");

 return oldbit;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
arch_test_and_change_bit(long nr, volatile unsigned long *addr)
{
 return ({ bool c; asm volatile (".pushsection .smp_locks,\"a\"\n" ".balign 4\n" ".long 671f - .\n" ".popsection\n" "671:" "\n\tlock; " " " "btcq" " " " %[val], " "%[var]" "\n\t/* output condition code " "c" "*/\n" : [var] "+m" (*addr), "=@cc" "c" (c) : [val] "Ir" (nr) : "memory"); c; });
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool constant_test_bit(long nr, const volatile unsigned long *addr)
{
 return ((1UL << (nr & (64 -1))) &
  (addr[nr >> 6])) != 0;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool constant_test_bit_acquire(long nr, const volatile unsigned long *addr)
{
 bool oldbit;

 asm volatile("testb %2,%1"
       "\n\t/* output condition code " "nz" "*/\n"
       : "=@cc" "nz" (oldbit)
       : "m" (((unsigned char *)addr)[nr >> 3]),
         "i" (1 << (nr & 7))
       :"memory");

 return oldbit;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool variable_test_bit(long nr, volatile const unsigned long *addr)
{
 bool oldbit;

 asm volatile(" " "btq" " " " %2,%1"
       "\n\t/* output condition code " "c" "*/\n"
       : "=@cc" "c" (oldbit)
       : "m" (*(unsigned long *)addr), "Ir" (nr) : "memory");

 return oldbit;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
arch_test_bit(unsigned long nr, const volatile unsigned long *addr)
{
 return __builtin_constant_p(nr) ? constant_test_bit(nr, addr) :
       variable_test_bit(nr, addr);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
arch_test_bit_acquire(unsigned long nr, const volatile unsigned long *addr)
{
 return __builtin_constant_p(nr) ? constant_test_bit_acquire(nr, addr) :
       variable_test_bit(nr, addr);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long variable__ffs(unsigned long word)
{
 asm("rep; bsf %1,%0"
  : "=r" (word)
  : "rm" (word));
 return word;
}
# 268 "./arch/x86/include/asm/bitops.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long variable_ffz(unsigned long word)
{
 asm("rep; bsf %1,%0"
  : "=r" (word)
  : "r" (~word));
 return word;
}
# 293 "./arch/x86/include/asm/bitops.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long __fls(unsigned long word)
{
 if (__builtin_constant_p(word))
  return 64 - 1 - __builtin_clzl(word);

 asm("bsr %1,%0"
     : "=r" (word)
     : "rm" (word));
 return word;
}




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) int variable_ffs(int x)
{
 int r;
# 321 "./arch/x86/include/asm/bitops.h"
 asm("bsfl %1,%0"
     : "=r" (r)
     : "rm" (x), "0" (-1));
# 334 "./arch/x86/include/asm/bitops.h"
 return r + 1;
}
# 361 "./arch/x86/include/asm/bitops.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) int fls(unsigned int x)
{
 int r;

 if (__builtin_constant_p(x))
  return x ? 32 - __builtin_clz(x) : 0;
# 378 "./arch/x86/include/asm/bitops.h"
 asm("bsrl %1,%0"
     : "=r" (r)
     : "rm" (x), "0" (-1));
# 391 "./arch/x86/include/asm/bitops.h"
 return r + 1;
}
# 406 "./arch/x86/include/asm/bitops.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) int fls64(__u64 x)
{
 int bitpos = -1;

 if (__builtin_constant_p(x))
  return x ? 64 - __builtin_clzll(x) : 0;





 asm("bsrq %1,%q0"
     : "+r" (bitpos)
     : "rm" (x));
 return bitpos + 1;
}




# 1 "./include/asm-generic/bitops/sched.h" 1





# 1 "./arch/x86/include/generated/uapi/asm/types.h" 1
# 7 "./include/asm-generic/bitops/sched.h" 2






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int sched_find_first_bit(const unsigned long *b)
{

 if (b[0])
  return (__builtin_constant_p(b[0]) ? (unsigned long)__builtin_ctzl(b[0]) : variable__ffs(b[0]));
 return (__builtin_constant_p(b[1]) ? (unsigned long)__builtin_ctzl(b[1]) : variable__ffs(b[1])) + 64;
# 30 "./include/asm-generic/bitops/sched.h"
}
# 427 "./arch/x86/include/asm/bitops.h" 2

# 1 "./arch/x86/include/asm/arch_hweight.h" 1
# 15 "./arch/x86/include/asm/arch_hweight.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned int __arch_hweight32(unsigned int w)
{
 unsigned int res;

 asm ("# ALT: oldnstr\n" "661:\n\t" "call __sw_hweight32" "\n662:\n" "# ALT: padding\n" ".skip -(((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")) > 0) * " "((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")),0x90\n" "663" ":\n" ".pushsection .altinstructions,\"a\"\n" " .long 661b - .\n" " .long " "664""1""f - .\n" " .4byte " "( 4*32+23)" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""1""f-""664""1""f" "\n" ".popsection\n" ".pushsection .altinstr_replacement, \"ax\"\n" "# ALT: replacement " "1" "\n" "664""1"":\n\t" "popcntl %1, %0" "\n" "665""1" ":\n" ".popsection\n"
    : "=""a" (res)
    : "D" (w));

 return res;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int __arch_hweight16(unsigned int w)
{
 return __arch_hweight32(w & 0xffff);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int __arch_hweight8(unsigned int w)
{
 return __arch_hweight32(w & 0xff);
}
# 43 "./arch/x86/include/asm/arch_hweight.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long __arch_hweight64(__u64 w)
{
 unsigned long res;

 asm ("# ALT: oldnstr\n" "661:\n\t" "call __sw_hweight64" "\n662:\n" "# ALT: padding\n" ".skip -(((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")) > 0) * " "((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")),0x90\n" "663" ":\n" ".pushsection .altinstructions,\"a\"\n" " .long 661b - .\n" " .long " "664""1""f - .\n" " .4byte " "( 4*32+23)" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""1""f-""664""1""f" "\n" ".popsection\n" ".pushsection .altinstr_replacement, \"ax\"\n" "# ALT: replacement " "1" "\n" "664""1"":\n\t" "popcntq %1, %0" "\n" "665""1" ":\n" ".popsection\n"
    : "=""a" (res)
    : "D" (w));

 return res;
}
# 429 "./arch/x86/include/asm/bitops.h" 2

# 1 "./include/asm-generic/bitops/const_hweight.h" 1
# 431 "./arch/x86/include/asm/bitops.h" 2

# 1 "./include/asm-generic/bitops/instrumented-atomic.h" 1
# 26 "./include/asm-generic/bitops/instrumented-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void set_bit(long nr, volatile unsigned long *addr)
{
 instrument_atomic_write(addr + ((nr) / 64), sizeof(long));
 arch_set_bit(nr, addr);
}
# 39 "./include/asm-generic/bitops/instrumented-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void clear_bit(long nr, volatile unsigned long *addr)
{
 instrument_atomic_write(addr + ((nr) / 64), sizeof(long));
 arch_clear_bit(nr, addr);
}
# 55 "./include/asm-generic/bitops/instrumented-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void change_bit(long nr, volatile unsigned long *addr)
{
 instrument_atomic_write(addr + ((nr) / 64), sizeof(long));
 arch_change_bit(nr, addr);
}
# 68 "./include/asm-generic/bitops/instrumented-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool test_and_set_bit(long nr, volatile unsigned long *addr)
{
 do { } while (0);
 instrument_atomic_read_write(addr + ((nr) / 64), sizeof(long));
 return arch_test_and_set_bit(nr, addr);
}
# 82 "./include/asm-generic/bitops/instrumented-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool test_and_clear_bit(long nr, volatile unsigned long *addr)
{
 do { } while (0);
 instrument_atomic_read_write(addr + ((nr) / 64), sizeof(long));
 return arch_test_and_clear_bit(nr, addr);
}
# 96 "./include/asm-generic/bitops/instrumented-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool test_and_change_bit(long nr, volatile unsigned long *addr)
{
 do { } while (0);
 instrument_atomic_read_write(addr + ((nr) / 64), sizeof(long));
 return arch_test_and_change_bit(nr, addr);
}
# 433 "./arch/x86/include/asm/bitops.h" 2
# 1 "./include/asm-generic/bitops/instrumented-non-atomic.h" 1
# 25 "./include/asm-generic/bitops/instrumented-non-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
___set_bit(unsigned long nr, volatile unsigned long *addr)
{
 instrument_write(addr + ((nr) / 64), sizeof(long));
 arch___set_bit(nr, addr);
}
# 41 "./include/asm-generic/bitops/instrumented-non-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
___clear_bit(unsigned long nr, volatile unsigned long *addr)
{
 instrument_write(addr + ((nr) / 64), sizeof(long));
 arch___clear_bit(nr, addr);
}
# 57 "./include/asm-generic/bitops/instrumented-non-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
___change_bit(unsigned long nr, volatile unsigned long *addr)
{
 instrument_write(addr + ((nr) / 64), sizeof(long));
 arch___change_bit(nr, addr);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void __instrument_read_write_bitop(long nr, volatile unsigned long *addr)
{
 if (0) {
# 77 "./include/asm-generic/bitops/instrumented-non-atomic.h"
  kcsan_check_access(addr + ((nr) / 64), sizeof(long), 0);




  instrument_write(addr + ((nr) / 64), sizeof(long));
 } else {
  instrument_read_write(addr + ((nr) / 64), sizeof(long));
 }
}
# 96 "./include/asm-generic/bitops/instrumented-non-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
___test_and_set_bit(unsigned long nr, volatile unsigned long *addr)
{
 __instrument_read_write_bitop(nr, addr);
 return arch___test_and_set_bit(nr, addr);
}
# 111 "./include/asm-generic/bitops/instrumented-non-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
___test_and_clear_bit(unsigned long nr, volatile unsigned long *addr)
{
 __instrument_read_write_bitop(nr, addr);
 return arch___test_and_clear_bit(nr, addr);
}
# 126 "./include/asm-generic/bitops/instrumented-non-atomic.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
___test_and_change_bit(unsigned long nr, volatile unsigned long *addr)
{
 __instrument_read_write_bitop(nr, addr);
 return arch___test_and_change_bit(nr, addr);
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
_test_bit(unsigned long nr, const volatile unsigned long *addr)
{
 instrument_atomic_read(addr + ((nr) / 64), sizeof(long));
 return arch_test_bit(nr, addr);
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool
_test_bit_acquire(unsigned long nr, const volatile unsigned long *addr)
{
 instrument_atomic_read(addr + ((nr) / 64), sizeof(long));
 return arch_test_bit_acquire(nr, addr);
}
# 434 "./arch/x86/include/asm/bitops.h" 2
# 1 "./include/asm-generic/bitops/instrumented-lock.h" 1
# 23 "./include/asm-generic/bitops/instrumented-lock.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void clear_bit_unlock(long nr, volatile unsigned long *addr)
{
 do { } while (0);
 instrument_atomic_write(addr + ((nr) / 64), sizeof(long));
 arch_clear_bit_unlock(nr, addr);
}
# 39 "./include/asm-generic/bitops/instrumented-lock.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __clear_bit_unlock(long nr, volatile unsigned long *addr)
{
 do { } while (0);
 instrument_write(addr + ((nr) / 64), sizeof(long));
 arch___clear_bit_unlock(nr, addr);
}
# 55 "./include/asm-generic/bitops/instrumented-lock.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool test_and_set_bit_lock(long nr, volatile unsigned long *addr)
{
 instrument_atomic_read_write(addr + ((nr) / 64), sizeof(long));
 return arch_test_and_set_bit_lock(nr, addr);
}
# 75 "./include/asm-generic/bitops/instrumented-lock.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool xor_unlock_is_negative_byte(unsigned long mask,
  volatile unsigned long *addr)
{
 do { } while (0);
 instrument_atomic_write(addr, sizeof(long));
 return arch_xor_unlock_is_negative_byte(mask, addr);
}
# 435 "./arch/x86/include/asm/bitops.h" 2

# 1 "./include/asm-generic/bitops/le.h" 1




# 1 "./arch/x86/include/generated/uapi/asm/types.h" 1
# 6 "./include/asm-generic/bitops/le.h" 2
# 19 "./include/asm-generic/bitops/le.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int test_bit_le(int nr, const void *addr)
{
 return ((__builtin_constant_p(nr ^ 0) && __builtin_constant_p((uintptr_t)(addr) != (uintptr_t)((void *)0)) && (uintptr_t)(addr) != (uintptr_t)((void *)0) && __builtin_constant_p(*(const unsigned long *)(addr))) ? const_test_bit(nr ^ 0, addr) : _test_bit(nr ^ 0, addr));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void set_bit_le(int nr, void *addr)
{
 set_bit(nr ^ 0, addr);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void clear_bit_le(int nr, void *addr)
{
 clear_bit(nr ^ 0, addr);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __set_bit_le(int nr, void *addr)
{
 ((__builtin_constant_p(nr ^ 0) && __builtin_constant_p((uintptr_t)(addr) != (uintptr_t)((void *)0)) && (uintptr_t)(addr) != (uintptr_t)((void *)0) && __builtin_constant_p(*(const unsigned long *)(addr))) ? generic___set_bit(nr ^ 0, addr) : ___set_bit(nr ^ 0, addr));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __clear_bit_le(int nr, void *addr)
{
 ((__builtin_constant_p(nr ^ 0) && __builtin_constant_p((uintptr_t)(addr) != (uintptr_t)((void *)0)) && (uintptr_t)(addr) != (uintptr_t)((void *)0) && __builtin_constant_p(*(const unsigned long *)(addr))) ? generic___clear_bit(nr ^ 0, addr) : ___clear_bit(nr ^ 0, addr));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int test_and_set_bit_le(int nr, void *addr)
{
 return test_and_set_bit(nr ^ 0, addr);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int test_and_clear_bit_le(int nr, void *addr)
{
 return test_and_clear_bit(nr ^ 0, addr);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int __test_and_set_bit_le(int nr, void *addr)
{
 return ((__builtin_constant_p(nr ^ 0) && __builtin_constant_p((uintptr_t)(addr) != (uintptr_t)((void *)0)) && (uintptr_t)(addr) != (uintptr_t)((void *)0) && __builtin_constant_p(*(const unsigned long *)(addr))) ? generic___test_and_set_bit(nr ^ 0, addr) : ___test_and_set_bit(nr ^ 0, addr));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int __test_and_clear_bit_le(int nr, void *addr)
{
 return ((__builtin_constant_p(nr ^ 0) && __builtin_constant_p((uintptr_t)(addr) != (uintptr_t)((void *)0)) && (uintptr_t)(addr) != (uintptr_t)((void *)0) && __builtin_constant_p(*(const unsigned long *)(addr))) ? generic___test_and_clear_bit(nr ^ 0, addr) : ___test_and_clear_bit(nr ^ 0, addr));
}
# 437 "./arch/x86/include/asm/bitops.h" 2

# 1 "./include/asm-generic/bitops/ext2-atomic-setbit.h" 1
# 439 "./arch/x86/include/asm/bitops.h" 2
# 69 "./include/linux/bitops.h" 2







_Static_assert(__builtin_types_compatible_p(typeof(arch___set_bit), typeof(generic___set_bit)) && __builtin_types_compatible_p(typeof(generic___set_bit), typeof(generic___set_bit)) && __builtin_types_compatible_p(typeof(___set_bit), typeof(generic___set_bit)), "__same_type(arch___set_bit, generic___set_bit) && __same_type(const___set_bit, generic___set_bit) && __same_type(___set_bit, generic___set_bit)");
_Static_assert(__builtin_types_compatible_p(typeof(arch___clear_bit), typeof(generic___clear_bit)) && __builtin_types_compatible_p(typeof(generic___clear_bit), typeof(generic___clear_bit)) && __builtin_types_compatible_p(typeof(___clear_bit), typeof(generic___clear_bit)), "__same_type(arch___clear_bit, generic___clear_bit) && __same_type(const___clear_bit, generic___clear_bit) && __same_type(___clear_bit, generic___clear_bit)");
_Static_assert(__builtin_types_compatible_p(typeof(arch___change_bit), typeof(generic___change_bit)) && __builtin_types_compatible_p(typeof(generic___change_bit), typeof(generic___change_bit)) && __builtin_types_compatible_p(typeof(___change_bit), typeof(generic___change_bit)), "__same_type(arch___change_bit, generic___change_bit) && __same_type(const___change_bit, generic___change_bit) && __same_type(___change_bit, generic___change_bit)");
_Static_assert(__builtin_types_compatible_p(typeof(arch___test_and_set_bit), typeof(generic___test_and_set_bit)) && __builtin_types_compatible_p(typeof(generic___test_and_set_bit), typeof(generic___test_and_set_bit)) && __builtin_types_compatible_p(typeof(___test_and_set_bit), typeof(generic___test_and_set_bit)), "__same_type(arch___test_and_set_bit, generic___test_and_set_bit) && __same_type(const___test_and_set_bit, generic___test_and_set_bit) && __same_type(___test_and_set_bit, generic___test_and_set_bit)");
_Static_assert(__builtin_types_compatible_p(typeof(arch___test_and_clear_bit), typeof(generic___test_and_clear_bit)) && __builtin_types_compatible_p(typeof(generic___test_and_clear_bit), typeof(generic___test_and_clear_bit)) && __builtin_types_compatible_p(typeof(___test_and_clear_bit), typeof(generic___test_and_clear_bit)), "__same_type(arch___test_and_clear_bit, generic___test_and_clear_bit) && __same_type(const___test_and_clear_bit, generic___test_and_clear_bit) && __same_type(___test_and_clear_bit, generic___test_and_clear_bit)");
_Static_assert(__builtin_types_compatible_p(typeof(arch___test_and_change_bit), typeof(generic___test_and_change_bit)) && __builtin_types_compatible_p(typeof(generic___test_and_change_bit), typeof(generic___test_and_change_bit)) && __builtin_types_compatible_p(typeof(___test_and_change_bit), typeof(generic___test_and_change_bit)), "__same_type(arch___test_and_change_bit, generic___test_and_change_bit) && __same_type(const___test_and_change_bit, generic___test_and_change_bit) && __same_type(___test_and_change_bit, generic___test_and_change_bit)");
_Static_assert(__builtin_types_compatible_p(typeof(arch_test_bit), typeof(generic_test_bit)) && __builtin_types_compatible_p(typeof(const_test_bit), typeof(generic_test_bit)) && __builtin_types_compatible_p(typeof(_test_bit), typeof(generic_test_bit)), "__same_type(arch_test_bit, generic_test_bit) && __same_type(const_test_bit, generic_test_bit) && __same_type(_test_bit, generic_test_bit)");
_Static_assert(__builtin_types_compatible_p(typeof(arch_test_bit_acquire), typeof(generic_test_bit_acquire)) && __builtin_types_compatible_p(typeof(generic_test_bit_acquire), typeof(generic_test_bit_acquire)) && __builtin_types_compatible_p(typeof(_test_bit_acquire), typeof(generic_test_bit_acquire)), "__same_type(arch_test_bit_acquire, generic_test_bit_acquire) && __same_type(const_test_bit_acquire, generic_test_bit_acquire) && __same_type(_test_bit_acquire, generic_test_bit_acquire)");



static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int get_bitmask_order(unsigned int count)
{
 int order;

 order = fls(count);
 return order;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long hweight_long(unsigned long w)
{
 return sizeof(w) == 4 ? (__builtin_constant_p(w) ? ((((unsigned int) ((!!((w) & (1ULL << 0))) + (!!((w) & (1ULL << 1))) + (!!((w) & (1ULL << 2))) + (!!((w) & (1ULL << 3))) + (!!((w) & (1ULL << 4))) + (!!((w) & (1ULL << 5))) + (!!((w) & (1ULL << 6))) + (!!((w) & (1ULL << 7))))) + ((unsigned int) ((!!(((w) >> 8) & (1ULL << 0))) + (!!(((w) >> 8) & (1ULL << 1))) + (!!(((w) >> 8) & (1ULL << 2))) + (!!(((w) >> 8) & (1ULL << 3))) + (!!(((w) >> 8) & (1ULL << 4))) + (!!(((w) >> 8) & (1ULL << 5))) + (!!(((w) >> 8) & (1ULL << 6))) + (!!(((w) >> 8) & (1ULL << 7)))))) + (((unsigned int) ((!!(((w) >> 16) & (1ULL << 0))) + (!!(((w) >> 16) & (1ULL << 1))) + (!!(((w) >> 16) & (1ULL << 2))) + (!!(((w) >> 16) & (1ULL << 3))) + (!!(((w) >> 16) & (1ULL << 4))) + (!!(((w) >> 16) & (1ULL << 5))) + (!!(((w) >> 16) & (1ULL << 6))) + (!!(((w) >> 16) & (1ULL << 7))))) + ((unsigned int) ((!!((((w) >> 16) >> 8) & (1ULL << 0))) + (!!((((w) >> 16) >> 8) & (1ULL << 1))) + (!!((((w) >> 16) >> 8) & (1ULL << 2))) + (!!((((w) >> 16) >> 8) & (1ULL << 3))) + (!!((((w) >> 16) >> 8) & (1ULL << 4))) + (!!((((w) >> 16) >> 8) & (1ULL << 5))) + (!!((((w) >> 16) >> 8) & (1ULL << 6))) + (!!((((w) >> 16) >> 8) & (1ULL << 7))))))) : __arch_hweight32(w)) : (__builtin_constant_p((__u64)w) ? (((((unsigned int) ((!!(((__u64)w) & (1ULL << 0))) + (!!(((__u64)w) & (1ULL << 1))) + (!!(((__u64)w) & (1ULL << 2))) + (!!(((__u64)w) & (1ULL << 3))) + (!!(((__u64)w) & (1ULL << 4))) + (!!(((__u64)w) & (1ULL << 5))) + (!!(((__u64)w) & (1ULL << 6))) + (!!(((__u64)w) & (1ULL << 7))))) + ((unsigned int) ((!!((((__u64)w) >> 8) & (1ULL << 0))) + (!!((((__u64)w) >> 8) & (1ULL << 1))) + (!!((((__u64)w) >> 8) & (1ULL << 2))) + (!!((((__u64)w) >> 8) & (1ULL << 3))) + (!!((((__u64)w) >> 8) & (1ULL << 4))) + (!!((((__u64)w) >> 8) & (1ULL << 5))) + (!!((((__u64)w) >> 8) & (1ULL << 6))) + (!!((((__u64)w) >> 8) & (1ULL << 7)))))) + (((unsigned int) ((!!((((__u64)w) >> 16) & (1ULL << 0))) + (!!((((__u64)w) >> 16) & (1ULL << 1))) + (!!((((__u64)w) >> 16) & (1ULL << 2))) + (!!((((__u64)w) >> 16) & (1ULL << 3))) + (!!((((__u64)w) >> 16) & (1ULL << 4))) + (!!((((__u64)w) >> 16) & (1ULL << 5))) + (!!((((__u64)w) >> 16) & (1ULL << 6))) + (!!((((__u64)w) >> 16) & (1ULL << 7))))) + ((unsigned int) ((!!(((((__u64)w) >> 16) >> 8) & (1ULL << 0))) + (!!(((((__u64)w) >> 16) >> 8) & (1ULL << 1))) + (!!(((((__u64)w) >> 16) >> 8) & (1ULL << 2))) + (!!(((((__u64)w) >> 16) >> 8) & (1ULL << 3))) + (!!(((((__u64)w) >> 16) >> 8) & (1ULL << 4))) + (!!(((((__u64)w) >> 16) >> 8) & (1ULL << 5))) + (!!(((((__u64)w) >> 16) >> 8) & (1ULL << 6))) + (!!(((((__u64)w) >> 16) >> 8) & (1ULL << 7))))))) + ((((unsigned int) ((!!((((__u64)w) >> 32) & (1ULL << 0))) + (!!((((__u64)w) >> 32) & (1ULL << 1))) + (!!((((__u64)w) >> 32) & (1ULL << 2))) + (!!((((__u64)w) >> 32) & (1ULL << 3))) + (!!((((__u64)w) >> 32) & (1ULL << 4))) + (!!((((__u64)w) >> 32) & (1ULL << 5))) + (!!((((__u64)w) >> 32) & (1ULL << 6))) + (!!((((__u64)w) >> 32) & (1ULL << 7))))) + ((unsigned int) ((!!(((((__u64)w) >> 32) >> 8) & (1ULL << 0))) + (!!(((((__u64)w) >> 32) >> 8) & (1ULL << 1))) + (!!(((((__u64)w) >> 32) >> 8) & (1ULL << 2))) + (!!(((((__u64)w) >> 32) >> 8) & (1ULL << 3))) + (!!(((((__u64)w) >> 32) >> 8) & (1ULL << 4))) + (!!(((((__u64)w) >> 32) >> 8) & (1ULL << 5))) + (!!(((((__u64)w) >> 32) >> 8) & (1ULL << 6))) + (!!(((((__u64)w) >> 32) >> 8) & (1ULL << 7)))))) + (((unsigned int) ((!!(((((__u64)w) >> 32) >> 16) & (1ULL << 0))) + (!!(((((__u64)w) >> 32) >> 16) & (1ULL << 1))) + (!!(((((__u64)w) >> 32) >> 16) & (1ULL << 2))) + (!!(((((__u64)w) >> 32) >> 16) & (1ULL << 3))) + (!!(((((__u64)w) >> 32) >> 16) & (1ULL << 4))) + (!!(((((__u64)w) >> 32) >> 16) & (1ULL << 5))) + (!!(((((__u64)w) >> 32) >> 16) & (1ULL << 6))) + (!!(((((__u64)w) >> 32) >> 16) & (1ULL << 7))))) + ((unsigned int) ((!!((((((__u64)w) >> 32) >> 16) >> 8) & (1ULL << 0))) + (!!((((((__u64)w) >> 32) >> 16) >> 8) & (1ULL << 1))) + (!!((((((__u64)w) >> 32) >> 16) >> 8) & (1ULL << 2))) + (!!((((((__u64)w) >> 32) >> 16) >> 8) & (1ULL << 3))) + (!!((((((__u64)w) >> 32) >> 16) >> 8) & (1ULL << 4))) + (!!((((((__u64)w) >> 32) >> 16) >> 8) & (1ULL << 5))) + (!!((((((__u64)w) >> 32) >> 16) >> 8) & (1ULL << 6))) + (!!((((((__u64)w) >> 32) >> 16) >> 8) & (1ULL << 7)))))))) : __arch_hweight64((__u64)w));
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __u64 rol64(__u64 word, unsigned int shift)
{
 return (word << (shift & 63)) | (word >> ((-shift) & 63));
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __u64 ror64(__u64 word, unsigned int shift)
{
 return (word >> (shift & 63)) | (word << ((-shift) & 63));
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __u32 rol32(__u32 word, unsigned int shift)
{
 return (word << (shift & 31)) | (word >> ((-shift) & 31));
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __u32 ror32(__u32 word, unsigned int shift)
{
 return (word >> (shift & 31)) | (word << ((-shift) & 31));
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __u16 rol16(__u16 word, unsigned int shift)
{
 return (word << (shift & 15)) | (word >> ((-shift) & 15));
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __u16 ror16(__u16 word, unsigned int shift)
{
 return (word >> (shift & 15)) | (word << ((-shift) & 15));
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __u8 rol8(__u8 word, unsigned int shift)
{
 return (word << (shift & 7)) | (word >> ((-shift) & 7));
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __u8 ror8(__u8 word, unsigned int shift)
{
 return (word >> (shift & 7)) | (word << ((-shift) & 7));
}
# 187 "./include/linux/bitops.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __s32 sign_extend32(__u32 value, int index)
{
 __u8 shift = 31 - index;
 return (__s32)(value << shift) >> shift;
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __s64 sign_extend64(__u64 value, int index)
{
 __u8 shift = 63 - index;
 return (__s64)(value << shift) >> shift;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned fls_long(unsigned long l)
{
 if (sizeof(l) == 4)
  return fls(l);
 return fls64(l);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int get_count_order(unsigned int count)
{
 if (count == 0)
  return -1;

 return fls(--count);
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int get_count_order_long(unsigned long l)
{
 if (l == 0UL)
  return -1;
 return (int)fls_long(--l);
}
# 240 "./include/linux/bitops.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long __ffs64(u64 word)
{






 return (__builtin_constant_p((unsigned long)word) ? (unsigned long)__builtin_ctzl((unsigned long)word) : variable__ffs((unsigned long)word));
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long fns(unsigned long word, unsigned int n)
{
 unsigned int bit;

 while (word) {
  bit = (__builtin_constant_p(word) ? (unsigned long)__builtin_ctzl(word) : variable__ffs(word));
  if (n-- == 0)
   return bit;
  ((__builtin_constant_p(bit) && __builtin_constant_p((uintptr_t)(&word) != (uintptr_t)((void *)0)) && (uintptr_t)(&word) != (uintptr_t)((void *)0) && __builtin_constant_p(*(const unsigned long *)(&word))) ? generic___clear_bit(bit, &word) : ___clear_bit(bit, &word));
 }

 return 64;
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void assign_bit(long nr, volatile unsigned long *addr,
           bool value)
{
 if (value)
  set_bit(nr, addr);
 else
  clear_bit(nr, addr);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void __assign_bit(long nr, volatile unsigned long *addr,
      bool value)
{
 if (value)
  ((__builtin_constant_p(nr) && __builtin_constant_p((uintptr_t)(addr) != (uintptr_t)((void *)0)) && (uintptr_t)(addr) != (uintptr_t)((void *)0) && __builtin_constant_p(*(const unsigned long *)(addr))) ? generic___set_bit(nr, addr) : ___set_bit(nr, addr));
 else
  ((__builtin_constant_p(nr) && __builtin_constant_p((uintptr_t)(addr) != (uintptr_t)((void *)0)) && (uintptr_t)(addr) != (uintptr_t)((void *)0) && __builtin_constant_p(*(const unsigned long *)(addr))) ? generic___clear_bit(nr, addr) : ___clear_bit(nr, addr));
}
# 24 "./include/linux/kernel.h" 2
# 1 "./include/linux/hex.h" 1






extern const char hex_asc[];



static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) char *hex_byte_pack(char *buf, u8 byte)
{
 *buf++ = hex_asc[((byte) & 0xf0) >> 4];
 *buf++ = hex_asc[((byte) & 0x0f)];
 return buf;
}

extern const char hex_asc_upper[];



static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) char *hex_byte_pack_upper(char *buf, u8 byte)
{
 *buf++ = hex_asc_upper[((byte) & 0xf0) >> 4];
 *buf++ = hex_asc_upper[((byte) & 0x0f)];
 return buf;
}

extern int hex_to_bin(unsigned char ch);
extern int __attribute__((__warn_unused_result__)) hex2bin(u8 *dst, const char *src, size_t count);
extern char *bin2hex(char *dst, const void *src, size_t count);

bool mac_pton(const char *s, u8 *mac);
# 25 "./include/linux/kernel.h" 2
# 1 "./include/linux/kstrtox.h" 1
# 9 "./include/linux/kstrtox.h"
int __attribute__((__warn_unused_result__)) _kstrtoul(const char *s, unsigned int base, unsigned long *res);
int __attribute__((__warn_unused_result__)) _kstrtol(const char *s, unsigned int base, long *res);

int __attribute__((__warn_unused_result__)) kstrtoull(const char *s, unsigned int base, unsigned long long *res);
int __attribute__((__warn_unused_result__)) kstrtoll(const char *s, unsigned int base, long long *res);
# 30 "./include/linux/kstrtox.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int __attribute__((__warn_unused_result__)) kstrtoul(const char *s, unsigned int base, unsigned long *res)
{




 if (sizeof(unsigned long) == sizeof(unsigned long long) &&
     __alignof__(unsigned long) == __alignof__(unsigned long long))
  return kstrtoull(s, base, (unsigned long long *)res);
 else
  return _kstrtoul(s, base, res);
}
# 58 "./include/linux/kstrtox.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int __attribute__((__warn_unused_result__)) kstrtol(const char *s, unsigned int base, long *res)
{




 if (sizeof(long) == sizeof(long long) &&
     __alignof__(long) == __alignof__(long long))
  return kstrtoll(s, base, (long long *)res);
 else
  return _kstrtol(s, base, res);
}

int __attribute__((__warn_unused_result__)) kstrtouint(const char *s, unsigned int base, unsigned int *res);
int __attribute__((__warn_unused_result__)) kstrtoint(const char *s, unsigned int base, int *res);

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int __attribute__((__warn_unused_result__)) kstrtou64(const char *s, unsigned int base, u64 *res)
{
 return kstrtoull(s, base, res);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int __attribute__((__warn_unused_result__)) kstrtos64(const char *s, unsigned int base, s64 *res)
{
 return kstrtoll(s, base, res);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int __attribute__((__warn_unused_result__)) kstrtou32(const char *s, unsigned int base, u32 *res)
{
 return kstrtouint(s, base, res);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int __attribute__((__warn_unused_result__)) kstrtos32(const char *s, unsigned int base, s32 *res)
{
 return kstrtoint(s, base, res);
}

int __attribute__((__warn_unused_result__)) kstrtou16(const char *s, unsigned int base, u16 *res);
int __attribute__((__warn_unused_result__)) kstrtos16(const char *s, unsigned int base, s16 *res);
int __attribute__((__warn_unused_result__)) kstrtou8(const char *s, unsigned int base, u8 *res);
int __attribute__((__warn_unused_result__)) kstrtos8(const char *s, unsigned int base, s8 *res);
int __attribute__((__warn_unused_result__)) kstrtobool(const char *s, bool *res);

int __attribute__((__warn_unused_result__)) kstrtoull_from_user(const char *s, size_t count, unsigned int base, unsigned long long *res);
int __attribute__((__warn_unused_result__)) kstrtoll_from_user(const char *s, size_t count, unsigned int base, long long *res);
int __attribute__((__warn_unused_result__)) kstrtoul_from_user(const char *s, size_t count, unsigned int base, unsigned long *res);
int __attribute__((__warn_unused_result__)) kstrtol_from_user(const char *s, size_t count, unsigned int base, long *res);
int __attribute__((__warn_unused_result__)) kstrtouint_from_user(const char *s, size_t count, unsigned int base, unsigned int *res);
int __attribute__((__warn_unused_result__)) kstrtoint_from_user(const char *s, size_t count, unsigned int base, int *res);
int __attribute__((__warn_unused_result__)) kstrtou16_from_user(const char *s, size_t count, unsigned int base, u16 *res);
int __attribute__((__warn_unused_result__)) kstrtos16_from_user(const char *s, size_t count, unsigned int base, s16 *res);
int __attribute__((__warn_unused_result__)) kstrtou8_from_user(const char *s, size_t count, unsigned int base, u8 *res);
int __attribute__((__warn_unused_result__)) kstrtos8_from_user(const char *s, size_t count, unsigned int base, s8 *res);
int __attribute__((__warn_unused_result__)) kstrtobool_from_user(const char *s, size_t count, bool *res);

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int __attribute__((__warn_unused_result__)) kstrtou64_from_user(const char *s, size_t count, unsigned int base, u64 *res)
{
 return kstrtoull_from_user(s, count, base, res);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int __attribute__((__warn_unused_result__)) kstrtos64_from_user(const char *s, size_t count, unsigned int base, s64 *res)
{
 return kstrtoll_from_user(s, count, base, res);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int __attribute__((__warn_unused_result__)) kstrtou32_from_user(const char *s, size_t count, unsigned int base, u32 *res)
{
 return kstrtouint_from_user(s, count, base, res);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int __attribute__((__warn_unused_result__)) kstrtos32_from_user(const char *s, size_t count, unsigned int base, s32 *res)
{
 return kstrtoint_from_user(s, count, base, res);
}
# 145 "./include/linux/kstrtox.h"
extern unsigned long simple_strtoul(const char *,char **,unsigned int);
extern long simple_strtol(const char *,char **,unsigned int);
extern unsigned long long simple_strtoull(const char *,char **,unsigned int);
extern long long simple_strtoll(const char *,char **,unsigned int);
# 26 "./include/linux/kernel.h" 2
# 1 "./include/linux/log2.h" 1
# 21 "./include/linux/log2.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __attribute__((const))
int __ilog2_u32(u32 n)
{
 return fls(n) - 1;
}



static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __attribute__((const))
int __ilog2_u64(u64 n)
{
 return fls64(n) - 1;
}
# 44 "./include/linux/log2.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((const))
bool is_power_of_2(unsigned long n)
{
 return (n != 0 && ((n & (n - 1)) == 0));
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((const))
unsigned long __roundup_pow_of_two(unsigned long n)
{
 return 1UL << fls_long(n - 1);
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((const))
unsigned long __rounddown_pow_of_two(unsigned long n)
{
 return 1UL << (fls_long(n) - 1);
}
# 198 "./include/linux/log2.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__const__))
int __order_base_2(unsigned long n)
{
 return n > 1 ? ( __builtin_constant_p(n - 1) ? ((n - 1) < 2 ? 0 : 63 - __builtin_clzll(n - 1)) : (sizeof(n - 1) <= 4) ? __ilog2_u32(n - 1) : __ilog2_u64(n - 1) ) + 1 : 0;
}
# 225 "./include/linux/log2.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((const))
int __bits_per(unsigned long n)
{
 if (n < 2)
  return 1;
 if (is_power_of_2(n))
  return ( __builtin_constant_p(n) ? ( ((n) == 0 || (n) == 1) ? 0 : ( __builtin_constant_p((n) - 1) ? (((n) - 1) < 2 ? 0 : 63 - __builtin_clzll((n) - 1)) : (sizeof((n) - 1) <= 4) ? __ilog2_u32((n) - 1) : __ilog2_u64((n) - 1) ) + 1) : __order_base_2(n) ) + 1;
 return ( __builtin_constant_p(n) ? ( ((n) == 0 || (n) == 1) ? 0 : ( __builtin_constant_p((n) - 1) ? (((n) - 1) < 2 ? 0 : 63 - __builtin_clzll((n) - 1)) : (sizeof((n) - 1) <= 4) ? __ilog2_u32((n) - 1) : __ilog2_u64((n) - 1) ) + 1) : __order_base_2(n) );
}
# 27 "./include/linux/kernel.h" 2
# 1 "./include/linux/math.h" 1





# 1 "./arch/x86/include/asm/div64.h" 1
# 81 "./arch/x86/include/asm/div64.h"
# 1 "./include/asm-generic/div64.h" 1
# 82 "./arch/x86/include/asm/div64.h" 2





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) u64 mul_u64_u64_div_u64(u64 a, u64 mul, u64 div)
{
 u64 q;

 asm ("mulq %2; divq %3" : "=a" (q)
    : "a" (a), "rm" (mul), "rm" (div)
    : "rdx");

 return q;
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) u64 mul_u64_u32_div(u64 a, u32 mul, u32 div)
{
 return mul_u64_u64_div_u64(a, mul, div);
}
# 7 "./include/linux/math.h" 2
# 115 "./include/linux/math.h"
struct s16_fract { __s16 numerator; __s16 denominator; };
struct u16_fract { __u16 numerator; __u16 denominator; };
struct s32_fract { __s32 numerator; __s32 denominator; };
struct u32_fract { __u32 numerator; __u32 denominator; };
# 191 "./include/linux/math.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) u32 reciprocal_scale(u32 val, u32 ep_ro)
{
 return (u32)(((u64) val * ep_ro) >> 32);
}

u64 int_pow(u64 base, unsigned int exp);
unsigned long int_sqrt(unsigned long);




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) u32 int_sqrt64(u64 x)
{
 return (u32)int_sqrt(x);
}
# 28 "./include/linux/kernel.h" 2
# 1 "./include/linux/minmax.h" 1
# 239 "./include/linux/minmax.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool in_range64(u64 val, u64 start, u64 len)
{
 return (val - start) < len;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool in_range32(u32 val, u32 start, u32 len)
{
 return (val - start) < len;
}
# 29 "./include/linux/kernel.h" 2

# 1 "./include/linux/panic.h" 1







struct pt_regs;

extern long (*panic_blink)(int state);
__attribute__((__format__(printf, 1, 2)))
void panic(const char *fmt, ...) __attribute__((__noreturn__)) ;
void nmi_panic(struct pt_regs *regs, const char *msg);
void check_panic_on_warn(const char *origin);
extern void oops_enter(void);
extern void oops_exit(void);
extern bool oops_may_print(void);

extern int panic_timeout;
extern unsigned long panic_print;
extern int panic_on_oops;
extern int panic_on_unrecovered_nmi;
extern int panic_on_io_nmi;
extern int panic_on_warn;

extern unsigned long panic_on_taint;
extern bool panic_on_taint_nousertaint;

extern int sysctl_panic_on_rcu_stall;
extern int sysctl_max_rcu_stall_to_panic;
extern int sysctl_panic_on_stackoverflow;

extern bool crash_kexec_post_notifiers;

extern void __stack_chk_fail(void);
void abort(void);






extern atomic_t panic_cpu;






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void set_arch_panic_timeout(int timeout, int arch_default_timeout)
{
 if (panic_timeout == arch_default_timeout)
  panic_timeout = timeout;
}
# 79 "./include/linux/panic.h"
struct taint_flag {
 char c_true;
 char c_false;
 bool module;
};

extern const struct taint_flag taint_flags[19];

enum lockdep_ok {
 LOCKDEP_STILL_OK,
 LOCKDEP_NOW_UNRELIABLE,
};

extern const char *print_tainted(void);
extern void add_taint(unsigned flag, enum lockdep_ok);
extern int test_taint(unsigned flag);
extern unsigned long get_taint(void);
# 31 "./include/linux/kernel.h" 2
# 1 "./include/linux/printk.h" 1






# 1 "./include/linux/kern_levels.h" 1
# 8 "./include/linux/printk.h" 2

# 1 "./include/linux/ratelimit_types.h" 1





# 1 "./include/uapi/linux/param.h" 1




# 1 "./arch/x86/include/generated/uapi/asm/param.h" 1
# 1 "./include/asm-generic/param.h" 1




# 1 "./include/uapi/asm-generic/param.h" 1
# 6 "./include/asm-generic/param.h" 2
# 2 "./arch/x86/include/generated/uapi/asm/param.h" 2
# 6 "./include/uapi/linux/param.h" 2
# 7 "./include/linux/ratelimit_types.h" 2
# 1 "./include/linux/spinlock_types_raw.h" 1






# 1 "./arch/x86/include/asm/spinlock_types.h" 1





# 1 "./include/asm-generic/qspinlock_types.h" 1
# 14 "./include/asm-generic/qspinlock_types.h"
typedef struct qspinlock {
 union {
  atomic_t val;







  struct {
   u8 locked;
   u8 pending;
  };
  struct {
   u16 locked_pending;
   u16 tail;
  };
# 43 "./include/asm-generic/qspinlock_types.h"
 };
} arch_spinlock_t;
# 7 "./arch/x86/include/asm/spinlock_types.h" 2
# 1 "./include/asm-generic/qrwlock_types.h" 1






# 1 "./arch/x86/include/asm/spinlock_types.h" 1
# 8 "./include/asm-generic/qrwlock_types.h" 2





typedef struct qrwlock {
 union {
  atomic_t cnts;
  struct {

   u8 wlocked;
   u8 __lstate[3];




  };
 };
 arch_spinlock_t wait_lock;
} arch_rwlock_t;
# 8 "./arch/x86/include/asm/spinlock_types.h" 2
# 8 "./include/linux/spinlock_types_raw.h" 2






typedef struct raw_spinlock {
 arch_spinlock_t raw_lock;







} raw_spinlock_t;
# 8 "./include/linux/ratelimit_types.h" 2







struct ratelimit_state {
 raw_spinlock_t lock;

 int interval;
 int burst;
 int printed;
 int missed;
 unsigned long begin;
 unsigned long flags;
};
# 44 "./include/linux/ratelimit_types.h"
extern int ___ratelimit(struct ratelimit_state *rs, const char *func);
# 10 "./include/linux/printk.h" 2
# 1 "./include/linux/once_lite.h" 1
# 11 "./include/linux/printk.h" 2

extern const char linux_banner[];
extern const char linux_proc_banner[];

extern int oops_in_progress;



static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int printk_get_level(const char *buffer)
{
 if (buffer[0] == '\001' && buffer[1]) {
  switch (buffer[1]) {
  case '0' ... '7':
  case 'c':
   return buffer[1];
  }
 }
 return 0;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) const char *printk_skip_level(const char *buffer)
{
 if (printk_get_level(buffer))
  return buffer + 2;

 return buffer;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) const char *printk_skip_headers(const char *buffer)
{
 while (printk_get_level(buffer))
  buffer = printk_skip_level(buffer);

 return buffer;
}
# 63 "./include/linux/printk.h"
extern int console_printk[];






extern void console_verbose(void);



extern char devkmsg_log_str[];
struct ctl_table;

extern int suppress_printk;

struct va_format {
 const char *fmt;
 va_list *va;
};
# 134 "./include/linux/printk.h"
extern __attribute__((__format__(printf, 1, 2)))
void early_printk(const char *fmt, ...);





struct dev_printk_info;


 __attribute__((__format__(printf, 4, 0)))
int vprintk_emit(int facility, int level,
   const struct dev_printk_info *dev_info,
   const char *fmt, va_list args);

 __attribute__((__format__(printf, 1, 0)))
int vprintk(const char *fmt, va_list args);

 __attribute__((__format__(printf, 1, 2)))
int _printk(const char *fmt, ...);




__attribute__((__format__(printf, 1, 2))) int _printk_deferred(const char *fmt, ...);

extern void __printk_safe_enter(void);
extern void __printk_safe_exit(void);
# 175 "./include/linux/printk.h"
extern int __printk_ratelimit(const char *func);

extern bool printk_timed_ratelimit(unsigned long *caller_jiffies,
       unsigned int interval_msec);

extern int printk_delay_msec;
extern int dmesg_restrict;

extern void wake_up_klogd(void);

char *log_buf_addr_get(void);
u32 log_buf_len_get(void);
void log_buf_vmcoreinfo_setup(void);
void __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep"))) setup_log_buf(int early);
__attribute__((__format__(printf, 1, 2))) void dump_stack_set_arch_desc(const char *fmt, ...);
void dump_stack_print_info(const char *log_lvl);
void show_regs_print_info(const char *log_lvl);
extern void dump_stack_lvl(const char *log_lvl) ;
extern void dump_stack(void) ;
void printk_trigger_flush(void);
# 276 "./include/linux/printk.h"
bool this_cpu_in_panic(void);


extern int __printk_cpu_sync_try_get(void);
extern void __printk_cpu_sync_wait(void);
extern void __printk_cpu_sync_put(void);
# 331 "./include/linux/printk.h"
extern int kptr_restrict;
# 350 "./include/linux/printk.h"
struct module;
# 704 "./include/linux/printk.h"
extern const struct file_operations kmsg_fops;

enum {
 DUMP_PREFIX_NONE,
 DUMP_PREFIX_ADDRESS,
 DUMP_PREFIX_OFFSET
};
extern int hex_dump_to_buffer(const void *buf, size_t len, int rowsize,
         int groupsize, char *linebuf, size_t linebuflen,
         bool ascii);

extern void print_hex_dump(const char *level, const char *prefix_str,
      int prefix_type, int rowsize, int groupsize,
      const void *buf, size_t len, bool ascii);
# 743 "./include/linux/printk.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void print_hex_dump_debug(const char *prefix_str, int prefix_type,
     int rowsize, int groupsize,
     const void *buf, size_t len, bool ascii)
{
}
# 32 "./include/linux/kernel.h" 2

# 1 "./include/linux/sprintf.h" 1







int num_to_str(char *buf, int size, unsigned long long num, unsigned int width);

__attribute__((__format__(printf, 2, 3))) int sprintf(char *buf, const char * fmt, ...);
__attribute__((__format__(printf, 2, 0))) int vsprintf(char *buf, const char *, va_list);
__attribute__((__format__(printf, 3, 4))) int snprintf(char *buf, size_t size, const char *fmt, ...);
__attribute__((__format__(printf, 3, 0))) int vsnprintf(char *buf, size_t size, const char *fmt, va_list args);
__attribute__((__format__(printf, 3, 4))) int scnprintf(char *buf, size_t size, const char *fmt, ...);
__attribute__((__format__(printf, 3, 0))) int vscnprintf(char *buf, size_t size, const char *fmt, va_list args);
__attribute__((__format__(printf, 2, 3))) __attribute__((__malloc__)) char *kasprintf(gfp_t gfp, const char *fmt, ...);
__attribute__((__format__(printf, 2, 0))) __attribute__((__malloc__)) char *kvasprintf(gfp_t gfp, const char *fmt, va_list args);
__attribute__((__format__(printf, 2, 0))) const char *kvasprintf_const(gfp_t gfp, const char *fmt, va_list args);

__attribute__((__format__(scanf, 2, 3))) int sscanf(const char *, const char *, ...);
__attribute__((__format__(scanf, 2, 0))) int vsscanf(const char *, const char *, va_list);


extern bool no_hash_pointers;
int no_hash_pointers_enable(char *str);
# 34 "./include/linux/kernel.h" 2
# 91 "./include/linux/kernel.h"
struct completion;
struct user;
# 101 "./include/linux/kernel.h"
extern int __cond_resched(void);

extern struct static_call_key __SCK__might_resched; extern typeof(__cond_resched) __SCT__might_resched;;

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void might_resched(void)
{
 ({ static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable___SCK__might_resched40 = (void *)&__SCK__might_resched;; (&__SCT__might_resched); })();
}
# 179 "./include/linux/kernel.h"
  static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __might_resched(const char *file, int line,
         unsigned int offsets) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __might_sleep(const char *file, int line) { }
# 197 "./include/linux/kernel.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void might_fault(void) { }


void do_exit(long error_code) __attribute__((__noreturn__));

extern int get_option(char **str, int *pint);
extern char *get_options(const char *str, int nints, int *ints);
extern unsigned long long memparse(const char *ptr, char **retptr);
extern bool parse_option_str(const char *str, const char *option);
extern char *next_arg(char *args, char **param, char **val);

extern int core_kernel_text(unsigned long addr);
extern int __kernel_text_address(unsigned long addr);
extern int kernel_text_address(unsigned long addr);
extern int func_ptr_is_kernel_text(void *ptr);

extern void bust_spinlocks(int yes);

extern int root_mountflags;

extern bool early_boot_irqs_disabled;





extern enum system_states {
 SYSTEM_BOOTING,
 SYSTEM_SCHEDULING,
 SYSTEM_FREEING_INITMEM,
 SYSTEM_RUNNING,
 SYSTEM_HALT,
 SYSTEM_POWER_OFF,
 SYSTEM_RESTART,
 SYSTEM_SUSPEND,
} system_state;
# 254 "./include/linux/kernel.h"
enum ftrace_dump_mode {
 DUMP_NONE,
 DUMP_ALL,
 DUMP_ORIG,
};


void tracing_on(void);
void tracing_off(void);
int tracing_is_on(void);
void tracing_snapshot(void);
void tracing_snapshot_alloc(void);

extern void tracing_start(void);
extern void tracing_stop(void);

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__format__(printf, 1, 2)))
void ____trace_printk_check_format(const char *fmt, ...)
{
}
# 333 "./include/linux/kernel.h"
extern __attribute__((__format__(printf, 2, 3)))
int __trace_bprintk(unsigned long ip, const char *fmt, ...);

extern __attribute__((__format__(printf, 2, 3)))
int __trace_printk(unsigned long ip, const char *fmt, ...);
# 374 "./include/linux/kernel.h"
extern int __trace_bputs(unsigned long ip, const char *str);
extern int __trace_puts(unsigned long ip, const char *str, int size);

extern void trace_dump_stack(int skip);
# 396 "./include/linux/kernel.h"
extern __attribute__((__format__(printf, 2, 0))) int
__ftrace_vbprintk(unsigned long ip, const char *fmt, va_list ap);

extern __attribute__((__format__(printf, 2, 0))) int
__ftrace_vprintk(unsigned long ip, const char *fmt, va_list ap);

extern void ftrace_dump(enum ftrace_dump_mode oops_dump_mode);
# 11 "./include/linux/cpumask.h" 2

# 1 "./include/linux/bitmap.h" 1
# 10 "./include/linux/bitmap.h"
# 1 "./include/linux/find.h" 1
# 11 "./include/linux/find.h"
unsigned long _find_next_bit(const unsigned long *addr1, unsigned long nbits,
    unsigned long start);
unsigned long _find_next_and_bit(const unsigned long *addr1, const unsigned long *addr2,
     unsigned long nbits, unsigned long start);
unsigned long _find_next_andnot_bit(const unsigned long *addr1, const unsigned long *addr2,
     unsigned long nbits, unsigned long start);
unsigned long _find_next_or_bit(const unsigned long *addr1, const unsigned long *addr2,
     unsigned long nbits, unsigned long start);
unsigned long _find_next_zero_bit(const unsigned long *addr, unsigned long nbits,
      unsigned long start);
extern unsigned long _find_first_bit(const unsigned long *addr, unsigned long size);
unsigned long __find_nth_bit(const unsigned long *addr, unsigned long size, unsigned long n);
unsigned long __find_nth_and_bit(const unsigned long *addr1, const unsigned long *addr2,
    unsigned long size, unsigned long n);
unsigned long __find_nth_andnot_bit(const unsigned long *addr1, const unsigned long *addr2,
     unsigned long size, unsigned long n);
unsigned long __find_nth_and_andnot_bit(const unsigned long *addr1, const unsigned long *addr2,
     const unsigned long *addr3, unsigned long size,
     unsigned long n);
extern unsigned long _find_first_and_bit(const unsigned long *addr1,
      const unsigned long *addr2, unsigned long size);
extern unsigned long _find_first_zero_bit(const unsigned long *addr, unsigned long size);
extern unsigned long _find_last_bit(const unsigned long *addr, unsigned long size);
# 53 "./include/linux/find.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned long find_next_bit(const unsigned long *addr, unsigned long size,
       unsigned long offset)
{
 if ((__builtin_constant_p(size) && (size) <= 64 && (size) > 0)) {
  unsigned long val;

  if (__builtin_expect(!!(offset >= size), 0))
   return size;

  val = *addr & ((((int)(sizeof(struct { int:(-!!(__builtin_choose_expr( (sizeof(int) == sizeof(*(8 ? ((void *)((long)((offset) > (size - 1)) * 0l)) : (int *)8))), (offset) > (size - 1), 0))); })))) + (((~(((0UL)))) - ((((1UL))) << (offset)) + 1) & (~(((0UL))) >> (64 - 1 - (size - 1)))));
  return val ? (__builtin_constant_p(val) ? (unsigned long)__builtin_ctzl(val) : variable__ffs(val)) : size;
 }

 return _find_next_bit(addr, size, offset);
}
# 82 "./include/linux/find.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned long find_next_and_bit(const unsigned long *addr1,
  const unsigned long *addr2, unsigned long size,
  unsigned long offset)
{
 if ((__builtin_constant_p(size) && (size) <= 64 && (size) > 0)) {
  unsigned long val;

  if (__builtin_expect(!!(offset >= size), 0))
   return size;

  val = *addr1 & *addr2 & ((((int)(sizeof(struct { int:(-!!(__builtin_choose_expr( (sizeof(int) == sizeof(*(8 ? ((void *)((long)((offset) > (size - 1)) * 0l)) : (int *)8))), (offset) > (size - 1), 0))); })))) + (((~(((0UL)))) - ((((1UL))) << (offset)) + 1) & (~(((0UL))) >> (64 - 1 - (size - 1)))));
  return val ? (__builtin_constant_p(val) ? (unsigned long)__builtin_ctzl(val) : variable__ffs(val)) : size;
 }

 return _find_next_and_bit(addr1, addr2, size, offset);
}
# 113 "./include/linux/find.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned long find_next_andnot_bit(const unsigned long *addr1,
  const unsigned long *addr2, unsigned long size,
  unsigned long offset)
{
 if ((__builtin_constant_p(size) && (size) <= 64 && (size) > 0)) {
  unsigned long val;

  if (__builtin_expect(!!(offset >= size), 0))
   return size;

  val = *addr1 & ~*addr2 & ((((int)(sizeof(struct { int:(-!!(__builtin_choose_expr( (sizeof(int) == sizeof(*(8 ? ((void *)((long)((offset) > (size - 1)) * 0l)) : (int *)8))), (offset) > (size - 1), 0))); })))) + (((~(((0UL)))) - ((((1UL))) << (offset)) + 1) & (~(((0UL))) >> (64 - 1 - (size - 1)))));
  return val ? (__builtin_constant_p(val) ? (unsigned long)__builtin_ctzl(val) : variable__ffs(val)) : size;
 }

 return _find_next_andnot_bit(addr1, addr2, size, offset);
}
# 143 "./include/linux/find.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned long find_next_or_bit(const unsigned long *addr1,
  const unsigned long *addr2, unsigned long size,
  unsigned long offset)
{
 if ((__builtin_constant_p(size) && (size) <= 64 && (size) > 0)) {
  unsigned long val;

  if (__builtin_expect(!!(offset >= size), 0))
   return size;

  val = (*addr1 | *addr2) & ((((int)(sizeof(struct { int:(-!!(__builtin_choose_expr( (sizeof(int) == sizeof(*(8 ? ((void *)((long)((offset) > (size - 1)) * 0l)) : (int *)8))), (offset) > (size - 1), 0))); })))) + (((~(((0UL)))) - ((((1UL))) << (offset)) + 1) & (~(((0UL))) >> (64 - 1 - (size - 1)))));
  return val ? (__builtin_constant_p(val) ? (unsigned long)__builtin_ctzl(val) : variable__ffs(val)) : size;
 }

 return _find_next_or_bit(addr1, addr2, size, offset);
}
# 172 "./include/linux/find.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned long find_next_zero_bit(const unsigned long *addr, unsigned long size,
     unsigned long offset)
{
 if ((__builtin_constant_p(size) && (size) <= 64 && (size) > 0)) {
  unsigned long val;

  if (__builtin_expect(!!(offset >= size), 0))
   return size;

  val = *addr | ~((((int)(sizeof(struct { int:(-!!(__builtin_choose_expr( (sizeof(int) == sizeof(*(8 ? ((void *)((long)((offset) > (size - 1)) * 0l)) : (int *)8))), (offset) > (size - 1), 0))); })))) + (((~(((0UL)))) - ((((1UL))) << (offset)) + 1) & (~(((0UL))) >> (64 - 1 - (size - 1)))));
  return val == ~0UL ? size : (__builtin_constant_p(val) ? (unsigned long)__builtin_ctzl(~val) : variable_ffz(val));
 }

 return _find_next_zero_bit(addr, size, offset);
}
# 199 "./include/linux/find.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned long find_first_bit(const unsigned long *addr, unsigned long size)
{
 if ((__builtin_constant_p(size) && (size) <= 64 && (size) > 0)) {
  unsigned long val = *addr & ((((int)(sizeof(struct { int:(-!!(__builtin_choose_expr( (sizeof(int) == sizeof(*(8 ? ((void *)((long)((0) > (size - 1)) * 0l)) : (int *)8))), (0) > (size - 1), 0))); })))) + (((~(((0UL)))) - ((((1UL))) << (0)) + 1) & (~(((0UL))) >> (64 - 1 - (size - 1)))));

  return val ? (__builtin_constant_p(val) ? (unsigned long)__builtin_ctzl(val) : variable__ffs(val)) : size;
 }

 return _find_first_bit(addr, size);
}
# 225 "./include/linux/find.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned long find_nth_bit(const unsigned long *addr, unsigned long size, unsigned long n)
{
 if (n >= size)
  return size;

 if ((__builtin_constant_p(size) && (size) <= 64 && (size) > 0)) {
  unsigned long val = *addr & ((((int)(sizeof(struct { int:(-!!(__builtin_choose_expr( (sizeof(int) == sizeof(*(8 ? ((void *)((long)((0) > (size - 1)) * 0l)) : (int *)8))), (0) > (size - 1), 0))); })))) + (((~(((0UL)))) - ((((1UL))) << (0)) + 1) & (~(((0UL))) >> (64 - 1 - (size - 1)))));

  return val ? fns(val, n) : size;
 }

 return __find_nth_bit(addr, size, n);
}
# 250 "./include/linux/find.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned long find_nth_and_bit(const unsigned long *addr1, const unsigned long *addr2,
    unsigned long size, unsigned long n)
{
 if (n >= size)
  return size;

 if ((__builtin_constant_p(size) && (size) <= 64 && (size) > 0)) {
  unsigned long val = *addr1 & *addr2 & ((((int)(sizeof(struct { int:(-!!(__builtin_choose_expr( (sizeof(int) == sizeof(*(8 ? ((void *)((long)((0) > (size - 1)) * 0l)) : (int *)8))), (0) > (size - 1), 0))); })))) + (((~(((0UL)))) - ((((1UL))) << (0)) + 1) & (~(((0UL))) >> (64 - 1 - (size - 1)))));

  return val ? fns(val, n) : size;
 }

 return __find_nth_and_bit(addr1, addr2, size, n);
}
# 277 "./include/linux/find.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned long find_nth_andnot_bit(const unsigned long *addr1, const unsigned long *addr2,
    unsigned long size, unsigned long n)
{
 if (n >= size)
  return size;

 if ((__builtin_constant_p(size) && (size) <= 64 && (size) > 0)) {
  unsigned long val = *addr1 & (~*addr2) & ((((int)(sizeof(struct { int:(-!!(__builtin_choose_expr( (sizeof(int) == sizeof(*(8 ? ((void *)((long)((0) > (size - 1)) * 0l)) : (int *)8))), (0) > (size - 1), 0))); })))) + (((~(((0UL)))) - ((((1UL))) << (0)) + 1) & (~(((0UL))) >> (64 - 1 - (size - 1)))));

  return val ? fns(val, n) : size;
 }

 return __find_nth_andnot_bit(addr1, addr2, size, n);
}
# 305 "./include/linux/find.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__))
unsigned long find_nth_and_andnot_bit(const unsigned long *addr1,
     const unsigned long *addr2,
     const unsigned long *addr3,
     unsigned long size, unsigned long n)
{
 if (n >= size)
  return size;

 if ((__builtin_constant_p(size) && (size) <= 64 && (size) > 0)) {
  unsigned long val = *addr1 & *addr2 & (~*addr3) & ((((int)(sizeof(struct { int:(-!!(__builtin_choose_expr( (sizeof(int) == sizeof(*(8 ? ((void *)((long)((0) > (size - 1)) * 0l)) : (int *)8))), (0) > (size - 1), 0))); })))) + (((~(((0UL)))) - ((((1UL))) << (0)) + 1) & (~(((0UL))) >> (64 - 1 - (size - 1)))));

  return val ? fns(val, n) : size;
 }

 return __find_nth_and_andnot_bit(addr1, addr2, addr3, size, n);
}
# 333 "./include/linux/find.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned long find_first_and_bit(const unsigned long *addr1,
     const unsigned long *addr2,
     unsigned long size)
{
 if ((__builtin_constant_p(size) && (size) <= 64 && (size) > 0)) {
  unsigned long val = *addr1 & *addr2 & ((((int)(sizeof(struct { int:(-!!(__builtin_choose_expr( (sizeof(int) == sizeof(*(8 ? ((void *)((long)((0) > (size - 1)) * 0l)) : (int *)8))), (0) > (size - 1), 0))); })))) + (((~(((0UL)))) - ((((1UL))) << (0)) + 1) & (~(((0UL))) >> (64 - 1 - (size - 1)))));

  return val ? (__builtin_constant_p(val) ? (unsigned long)__builtin_ctzl(val) : variable__ffs(val)) : size;
 }

 return _find_first_and_bit(addr1, addr2, size);
}
# 357 "./include/linux/find.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned long find_first_zero_bit(const unsigned long *addr, unsigned long size)
{
 if ((__builtin_constant_p(size) && (size) <= 64 && (size) > 0)) {
  unsigned long val = *addr | ~((((int)(sizeof(struct { int:(-!!(__builtin_choose_expr( (sizeof(int) == sizeof(*(8 ? ((void *)((long)((0) > (size - 1)) * 0l)) : (int *)8))), (0) > (size - 1), 0))); })))) + (((~(((0UL)))) - ((((1UL))) << (0)) + 1) & (~(((0UL))) >> (64 - 1 - (size - 1)))));

  return val == ~0UL ? size : (__builtin_constant_p(val) ? (unsigned long)__builtin_ctzl(~val) : variable_ffz(val));
 }

 return _find_first_zero_bit(addr, size);
}
# 378 "./include/linux/find.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned long find_last_bit(const unsigned long *addr, unsigned long size)
{
 if ((__builtin_constant_p(size) && (size) <= 64 && (size) > 0)) {
  unsigned long val = *addr & ((((int)(sizeof(struct { int:(-!!(__builtin_choose_expr( (sizeof(int) == sizeof(*(8 ? ((void *)((long)((0) > (size - 1)) * 0l)) : (int *)8))), (0) > (size - 1), 0))); })))) + (((~(((0UL)))) - ((((1UL))) << (0)) + 1) & (~(((0UL))) >> (64 - 1 - (size - 1)))));

  return val ? __fls(val) : size;
 }

 return _find_last_bit(addr, size);
}
# 401 "./include/linux/find.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned long find_next_and_bit_wrap(const unsigned long *addr1,
     const unsigned long *addr2,
     unsigned long size, unsigned long offset)
{
 unsigned long bit = find_next_and_bit(addr1, addr2, size, offset);

 if (bit < size)
  return bit;

 bit = find_first_and_bit(addr1, addr2, offset);
 return bit < offset ? bit : size;
}
# 424 "./include/linux/find.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned long find_next_bit_wrap(const unsigned long *addr,
     unsigned long size, unsigned long offset)
{
 unsigned long bit = find_next_bit(addr, size, offset);

 if (bit < size)
  return bit;

 bit = find_first_bit(addr, offset);
 return bit < offset ? bit : size;
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned long __for_each_wrap(const unsigned long *bitmap, unsigned long size,
     unsigned long start, unsigned long n)
{
 unsigned long bit;


 if (n > start) {

  bit = find_next_bit(bitmap, size, n);
  if (bit < size)
   return bit;


  n = 0;
 }


 bit = find_next_bit(bitmap, start, n);
 return bit < start ? bit : size;
}
# 473 "./include/linux/find.h"
extern unsigned long find_next_clump8(unsigned long *clump,
          const unsigned long *addr,
          unsigned long size, unsigned long offset);






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long find_next_zero_bit_le(const void *addr,
  unsigned long size, unsigned long offset)
{
 return find_next_zero_bit(addr, size, offset);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long find_next_bit_le(const void *addr,
  unsigned long size, unsigned long offset)
{
 return find_next_bit(addr, size, offset);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long find_first_zero_bit_le(const void *addr,
  unsigned long size)
{
 return find_first_zero_bit(addr, size);
}
# 11 "./include/linux/bitmap.h" 2

# 1 "./include/linux/string.h" 1
# 9 "./include/linux/string.h"
# 1 "./include/linux/err.h" 1







# 1 "./arch/x86/include/generated/uapi/asm/errno.h" 1
# 9 "./include/linux/err.h" 2
# 39 "./include/linux/err.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void * __attribute__((__warn_unused_result__)) ERR_PTR(long error)
{
 return (void *) error;
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) long __attribute__((__warn_unused_result__)) PTR_ERR( const void *ptr)
{
 return (long) ptr;
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool __attribute__((__warn_unused_result__)) IS_ERR( const void *ptr)
{
 return __builtin_expect(!!((unsigned long)(void *)((unsigned long)ptr) >= (unsigned long)-4095), 0);
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool __attribute__((__warn_unused_result__)) IS_ERR_OR_NULL( const void *ptr)
{
 return __builtin_expect(!!(!ptr), 0) || __builtin_expect(!!((unsigned long)(void *)((unsigned long)ptr) >= (unsigned long)-4095), 0);
}
# 82 "./include/linux/err.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void * __attribute__((__warn_unused_result__)) ERR_CAST( const void *ptr)
{

 return (void *) ptr;
}
# 105 "./include/linux/err.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int __attribute__((__warn_unused_result__)) PTR_ERR_OR_ZERO( const void *ptr)
{
 if (IS_ERR(ptr))
  return PTR_ERR(ptr);
 else
  return 0;
}
# 10 "./include/linux/string.h" 2

# 1 "./include/linux/overflow.h" 1
# 51 "./include/linux/overflow.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool __attribute__((__warn_unused_result__)) __must_check_overflow(bool overflow)
{
 return __builtin_expect(!!(overflow), 0);
}
# 189 "./include/linux/overflow.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) size_t __attribute__((__warn_unused_result__)) size_mul(size_t factor1, size_t factor2)
{
 size_t bytes;

 if (__must_check_overflow(__builtin_mul_overflow(factor1, factor2, &bytes)))
  return (~(size_t)0);

 return bytes;
}
# 208 "./include/linux/overflow.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) size_t __attribute__((__warn_unused_result__)) size_add(size_t addend1, size_t addend2)
{
 size_t bytes;

 if (__must_check_overflow(__builtin_add_overflow(addend1, addend2, &bytes)))
  return (~(size_t)0);

 return bytes;
}
# 229 "./include/linux/overflow.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) size_t __attribute__((__warn_unused_result__)) size_sub(size_t minuend, size_t subtrahend)
{
 size_t bytes;

 if (minuend == (~(size_t)0) || subtrahend == (~(size_t)0) ||
     __must_check_overflow(__builtin_sub_overflow(minuend, subtrahend, &bytes)))
  return (~(size_t)0);

 return bytes;
}
# 12 "./include/linux/string.h" 2

# 1 "./include/uapi/linux/string.h" 1
# 14 "./include/linux/string.h" 2

extern char *strndup_user(const char *, long);
extern void *memdup_user(const void *, size_t);
extern void *vmemdup_user(const void *, size_t);
extern void *memdup_user_nul(const void *, size_t);
# 29 "./include/linux/string.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void *memdup_array_user(const void *src, size_t n, size_t size)
{
 size_t nbytes;

 if (__must_check_overflow(__builtin_mul_overflow(n, size, &nbytes)))
  return ERR_PTR(-75);

 return memdup_user(src, nbytes);
}
# 48 "./include/linux/string.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void *vmemdup_array_user(const void *src, size_t n, size_t size)
{
 size_t nbytes;

 if (__must_check_overflow(__builtin_mul_overflow(n, size, &nbytes)))
  return ERR_PTR(-75);

 return vmemdup_user(src, nbytes);
}




# 1 "./arch/x86/include/asm/string.h" 1




# 1 "./arch/x86/include/asm/string_64.h" 1
# 18 "./arch/x86/include/asm/string_64.h"
extern void *memcpy(void *to, const void *from, size_t len);
extern void *__memcpy(void *to, const void *from, size_t len);


void *memset(void *s, int c, size_t n);
void *__memset(void *s, int c, size_t n);







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void *memset16(uint16_t *s, uint16_t v, size_t n)
{
 long d0, d1;
 asm volatile("rep\n\t"
       "stosw"
       : "=&c" (d0), "=&D" (d1)
       : "a" (v), "1" (s), "0" (n)
       : "memory");
 return s;
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void *memset32(uint32_t *s, uint32_t v, size_t n)
{
 long d0, d1;
 asm volatile("rep\n\t"
       "stosl"
       : "=&c" (d0), "=&D" (d1)
       : "a" (v), "1" (s), "0" (n)
       : "memory");
 return s;
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void *memset64(uint64_t *s, uint64_t v, size_t n)
{
 long d0, d1;
 asm volatile("rep\n\t"
       "stosq"
       : "=&c" (d0), "=&D" (d1)
       : "a" (v), "1" (s), "0" (n)
       : "memory");
 return s;
}



void *memmove(void *dest, const void *src, size_t count);
void *__memmove(void *dest, const void *src, size_t count);

int memcmp(const void *cs, const void *ct, size_t count);
size_t strlen(const char *s);
char *strcpy(char *dest, const char *src);
char *strcat(char *dest, const char *src);
int strcmp(const char *cs, const char *ct);



void __memcpy_flushcache(void *dst, const void *src, size_t cnt);
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void memcpy_flushcache(void *dst, const void *src, size_t cnt)
{
 if (__builtin_constant_p(cnt)) {
  switch (cnt) {
   case 4:
    asm ("movntil %1, %0" : "=m"(*(u32 *)dst) : "r"(*(u32 *)src));
    return;
   case 8:
    asm ("movntiq %1, %0" : "=m"(*(u64 *)dst) : "r"(*(u64 *)src));
    return;
   case 16:
    asm ("movntiq %1, %0" : "=m"(*(u64 *)dst) : "r"(*(u64 *)src));
    asm ("movntiq %1, %0" : "=m"(*(u64 *)(dst + 8)) : "r"(*(u64 *)(src + 8)));
    return;
  }
 }
 __memcpy_flushcache(dst, src, cnt);
}
# 6 "./arch/x86/include/asm/string.h" 2
# 62 "./include/linux/string.h" 2


extern char * strcpy(char *,const char *);


extern char * strncpy(char *,const char *, __kernel_size_t);


ssize_t strscpy(char *, const char *, size_t);



ssize_t strscpy_pad(char *dest, const char *src, size_t count);


extern char * strcat(char *, const char *);


extern char * strncat(char *, const char *, __kernel_size_t);


extern size_t strlcat(char *, const char *, __kernel_size_t);


extern int strcmp(const char *,const char *);


extern int strncmp(const char *,const char *,__kernel_size_t);


extern int strcasecmp(const char *s1, const char *s2);


extern int strncasecmp(const char *s1, const char *s2, size_t n);


extern char * strchr(const char *,int);


extern char * strchrnul(const char *,int);

extern char * strnchrnul(const char *, size_t, int);

extern char * strnchr(const char *, size_t, int);


extern char * strrchr(const char *,int);

extern char * __attribute__((__warn_unused_result__)) skip_spaces(const char *);

extern char *strim(char *);

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__warn_unused_result__)) char *strstrip(char *str)
{
 return strim(str);
}


extern char * strstr(const char *, const char *);


extern char * strnstr(const char *, const char *, size_t);


extern __kernel_size_t strlen(const char *);


extern __kernel_size_t strnlen(const char *,__kernel_size_t);


extern char * strpbrk(const char *,const char *);


extern char * strsep(char **,const char *);


extern __kernel_size_t strspn(const char *,const char *);


extern __kernel_size_t strcspn(const char *,const char *);
# 160 "./include/linux/string.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void *memset_l(unsigned long *p, unsigned long v,
  __kernel_size_t n)
{
 if (64 == 32)
  return memset32((uint32_t *)p, v, n);
 else
  return memset64((uint64_t *)p, v, n);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void *memset_p(void **p, void *v, __kernel_size_t n)
{
 if (64 == 32)
  return memset32((uint32_t *)p, (uintptr_t)v, n);
 else
  return memset64((uint64_t *)p, (uintptr_t)v, n);
}

extern void **__memcat_p(void **a, void **b);
# 191 "./include/linux/string.h"
extern void * memscan(void *,int,__kernel_size_t);


extern int memcmp(const void *,const void *,__kernel_size_t);


extern int bcmp(const void *,const void *,__kernel_size_t);


extern void * memchr(const void *,int,__kernel_size_t);
# 209 "./include/linux/string.h"
void *memchr_inv(const void *s, int c, size_t n);
char *strreplace(char *str, char old, char new);

extern void kfree_const(const void *x);

extern char *kstrdup(const char *s, gfp_t gfp) __attribute__((__malloc__));
extern const char *kstrdup_const(const char *s, gfp_t gfp);
extern char *kstrndup(const char *s, size_t len, gfp_t gfp);
extern void *kmemdup(const void *src, size_t len, gfp_t gfp) __attribute__((__alloc_size__(2)));
extern void *kvmemdup(const void *src, size_t len, gfp_t gfp) __attribute__((__alloc_size__(2)));
extern char *kmemdup_nul(const char *s, size_t len, gfp_t gfp);

extern char **argv_split(gfp_t gfp, const char *str, int *argcp);
extern void argv_free(char **argv);

extern bool sysfs_streq(const char *s1, const char *s2);
int match_string(const char * const *array, size_t n, const char *string);
int __sysfs_match_string(const char * const *array, size_t n, const char *s);
# 238 "./include/linux/string.h"
int vbin_printf(u32 *bin_buf, size_t size, const char *fmt, va_list args);
int bstr_printf(char *buf, size_t size, const char *fmt, const u32 *bin_buf);
int bprintf(u32 *bin_buf, size_t size, const char *fmt, ...) __attribute__((__format__(printf, 3, 4)));


extern ssize_t memory_read_from_buffer(void *to, size_t count, loff_t *ppos,
           const void *from, size_t available);

int ptr_to_hashval(const void *ptr, unsigned long *hashval_out);






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool strstarts(const char *str, const char *prefix)
{
 return strncmp(str, prefix, strlen(prefix)) == 0;
}

size_t memweight(const void *ptr, size_t bytes);
# 274 "./include/linux/string.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void memzero_explicit(void *s, size_t count)
{
 memset(s, 0, count);
 __asm__ __volatile__("": :"r"(s) :"memory");
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) const char *kbasename(const char *path)
{
 const char *tail = strrchr(path, '/');
 return tail ? tail + 1 : path;
}
# 299 "./include/linux/string.h"
void memcpy_and_pad(void *dest, size_t dest_len, const void *src, size_t count,
      int pad);
# 398 "./include/linux/string.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) size_t str_has_prefix(const char *str, const char *prefix)
{
 size_t len = strlen(prefix);
 return strncmp(str, prefix, len) == 0 ? len : 0;
}
# 13 "./include/linux/bitmap.h" 2

# 1 "./include/linux/bitmap-str.h" 1




int bitmap_parse_user(const char *ubuf, unsigned int ulen, unsigned long *dst, int nbits);
int bitmap_print_to_pagebuf(bool list, char *buf, const unsigned long *maskp, int nmaskbits);
extern int bitmap_print_bitmask_to_buf(char *buf, const unsigned long *maskp,
     int nmaskbits, loff_t off, size_t count);
extern int bitmap_print_list_to_buf(char *buf, const unsigned long *maskp,
     int nmaskbits, loff_t off, size_t count);
int bitmap_parse(const char *buf, unsigned int buflen, unsigned long *dst, int nbits);
int bitmap_parselist(const char *buf, unsigned long *maskp, int nmaskbits);
int bitmap_parselist_user(const char *ubuf, unsigned int ulen,
     unsigned long *dst, int nbits);
# 15 "./include/linux/bitmap.h" 2

struct device;
# 124 "./include/linux/bitmap.h"
unsigned long *bitmap_alloc(unsigned int nbits, gfp_t flags);
unsigned long *bitmap_zalloc(unsigned int nbits, gfp_t flags);
unsigned long *bitmap_alloc_node(unsigned int nbits, gfp_t flags, int node);
unsigned long *bitmap_zalloc_node(unsigned int nbits, gfp_t flags, int node);
void bitmap_free(const unsigned long *bitmap);


unsigned long *devm_bitmap_alloc(struct device *dev,
     unsigned int nbits, gfp_t flags);
unsigned long *devm_bitmap_zalloc(struct device *dev,
      unsigned int nbits, gfp_t flags);





bool __bitmap_equal(const unsigned long *bitmap1,
      const unsigned long *bitmap2, unsigned int nbits);
bool __attribute__((__pure__)) __bitmap_or_equal(const unsigned long *src1,
         const unsigned long *src2,
         const unsigned long *src3,
         unsigned int nbits);
void __bitmap_complement(unsigned long *dst, const unsigned long *src,
    unsigned int nbits);
void __bitmap_shift_right(unsigned long *dst, const unsigned long *src,
     unsigned int shift, unsigned int nbits);
void __bitmap_shift_left(unsigned long *dst, const unsigned long *src,
    unsigned int shift, unsigned int nbits);
void bitmap_cut(unsigned long *dst, const unsigned long *src,
  unsigned int first, unsigned int cut, unsigned int nbits);
bool __bitmap_and(unsigned long *dst, const unsigned long *bitmap1,
   const unsigned long *bitmap2, unsigned int nbits);
void __bitmap_or(unsigned long *dst, const unsigned long *bitmap1,
   const unsigned long *bitmap2, unsigned int nbits);
void __bitmap_xor(unsigned long *dst, const unsigned long *bitmap1,
    const unsigned long *bitmap2, unsigned int nbits);
bool __bitmap_andnot(unsigned long *dst, const unsigned long *bitmap1,
      const unsigned long *bitmap2, unsigned int nbits);
void __bitmap_replace(unsigned long *dst,
        const unsigned long *old, const unsigned long *new,
        const unsigned long *mask, unsigned int nbits);
bool __bitmap_intersects(const unsigned long *bitmap1,
    const unsigned long *bitmap2, unsigned int nbits);
bool __bitmap_subset(const unsigned long *bitmap1,
       const unsigned long *bitmap2, unsigned int nbits);
unsigned int __bitmap_weight(const unsigned long *bitmap, unsigned int nbits);
unsigned int __bitmap_weight_and(const unsigned long *bitmap1,
     const unsigned long *bitmap2, unsigned int nbits);
void __bitmap_set(unsigned long *map, unsigned int start, int len);
void __bitmap_clear(unsigned long *map, unsigned int start, int len);

unsigned long bitmap_find_next_zero_area_off(unsigned long *map,
          unsigned long size,
          unsigned long start,
          unsigned int nr,
          unsigned long align_mask,
          unsigned long align_offset);
# 194 "./include/linux/bitmap.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long
bitmap_find_next_zero_area(unsigned long *map,
      unsigned long size,
      unsigned long start,
      unsigned int nr,
      unsigned long align_mask)
{
 return bitmap_find_next_zero_area_off(map, size, start, nr,
           align_mask, 0);
}

void bitmap_remap(unsigned long *dst, const unsigned long *src,
  const unsigned long *old, const unsigned long *new, unsigned int nbits);
int bitmap_bitremap(int oldbit,
  const unsigned long *old, const unsigned long *new, int bits);
void bitmap_onto(unsigned long *dst, const unsigned long *orig,
  const unsigned long *relmap, unsigned int bits);
void bitmap_fold(unsigned long *dst, const unsigned long *orig,
  unsigned int sz, unsigned int nbits);




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void bitmap_zero(unsigned long *dst, unsigned int nbits)
{
 unsigned int len = (((nbits) + ((sizeof(long) * 8)) - 1) / ((sizeof(long) * 8))) * sizeof(unsigned long);

 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  *dst = 0;
 else
  memset(dst, 0, len);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void bitmap_fill(unsigned long *dst, unsigned int nbits)
{
 unsigned int len = (((nbits) + ((sizeof(long) * 8)) - 1) / ((sizeof(long) * 8))) * sizeof(unsigned long);

 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  *dst = ~0UL;
 else
  memset(dst, 0xff, len);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void bitmap_copy(unsigned long *dst, const unsigned long *src,
   unsigned int nbits)
{
 unsigned int len = (((nbits) + ((sizeof(long) * 8)) - 1) / ((sizeof(long) * 8))) * sizeof(unsigned long);

 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  *dst = *src;
 else
  memcpy(dst, src, len);
}




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void bitmap_copy_clear_tail(unsigned long *dst,
  const unsigned long *src, unsigned int nbits)
{
 bitmap_copy(dst, src, nbits);
 if (nbits % 64)
  dst[nbits / 64] &= (~0UL >> (-(nbits) & (64 - 1)));
}
# 268 "./include/linux/bitmap.h"
void bitmap_from_arr32(unsigned long *bitmap, const u32 *buf,
       unsigned int nbits);
void bitmap_to_arr32(u32 *buf, const unsigned long *bitmap,
       unsigned int nbits);
# 295 "./include/linux/bitmap.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool bitmap_and(unsigned long *dst, const unsigned long *src1,
   const unsigned long *src2, unsigned int nbits)
{
 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  return (*dst = *src1 & *src2 & (~0UL >> (-(nbits) & (64 - 1)))) != 0;
 return __bitmap_and(dst, src1, src2, nbits);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void bitmap_or(unsigned long *dst, const unsigned long *src1,
   const unsigned long *src2, unsigned int nbits)
{
 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  *dst = *src1 | *src2;
 else
  __bitmap_or(dst, src1, src2, nbits);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void bitmap_xor(unsigned long *dst, const unsigned long *src1,
   const unsigned long *src2, unsigned int nbits)
{
 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  *dst = *src1 ^ *src2;
 else
  __bitmap_xor(dst, src1, src2, nbits);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool bitmap_andnot(unsigned long *dst, const unsigned long *src1,
   const unsigned long *src2, unsigned int nbits)
{
 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  return (*dst = *src1 & ~(*src2) & (~0UL >> (-(nbits) & (64 - 1)))) != 0;
 return __bitmap_andnot(dst, src1, src2, nbits);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void bitmap_complement(unsigned long *dst, const unsigned long *src,
   unsigned int nbits)
{
 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  *dst = ~(*src);
 else
  __bitmap_complement(dst, src, nbits);
}
# 345 "./include/linux/bitmap.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool bitmap_equal(const unsigned long *src1,
    const unsigned long *src2, unsigned int nbits)
{
 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  return !((*src1 ^ *src2) & (~0UL >> (-(nbits) & (64 - 1))));
 if (__builtin_constant_p(nbits & (8 - 1)) &&
     (((nbits) & ((typeof(nbits))(8) - 1)) == 0))
  return !memcmp(src1, src2, nbits / 8);
 return __bitmap_equal(src1, src2, nbits);
}
# 365 "./include/linux/bitmap.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool bitmap_or_equal(const unsigned long *src1,
       const unsigned long *src2,
       const unsigned long *src3,
       unsigned int nbits)
{
 if (!(__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  return __bitmap_or_equal(src1, src2, src3, nbits);

 return !(((*src1 | *src2) ^ *src3) & (~0UL >> (-(nbits) & (64 - 1))));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool bitmap_intersects(const unsigned long *src1,
         const unsigned long *src2,
         unsigned int nbits)
{
 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  return ((*src1 & *src2) & (~0UL >> (-(nbits) & (64 - 1)))) != 0;
 else
  return __bitmap_intersects(src1, src2, nbits);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool bitmap_subset(const unsigned long *src1,
     const unsigned long *src2, unsigned int nbits)
{
 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  return ! ((*src1 & ~(*src2)) & (~0UL >> (-(nbits) & (64 - 1))));
 else
  return __bitmap_subset(src1, src2, nbits);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool bitmap_empty(const unsigned long *src, unsigned nbits)
{
 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  return ! (*src & (~0UL >> (-(nbits) & (64 - 1))));

 return find_first_bit(src, nbits) == nbits;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool bitmap_full(const unsigned long *src, unsigned int nbits)
{
 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  return ! (~(*src) & (~0UL >> (-(nbits) & (64 - 1))));

 return find_first_zero_bit(src, nbits) == nbits;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__))
unsigned int bitmap_weight(const unsigned long *src, unsigned int nbits)
{
 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  return hweight_long(*src & (~0UL >> (-(nbits) & (64 - 1))));
 return __bitmap_weight(src, nbits);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__))
unsigned long bitmap_weight_and(const unsigned long *src1,
    const unsigned long *src2, unsigned int nbits)
{
 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  return hweight_long(*src1 & *src2 & (~0UL >> (-(nbits) & (64 - 1))));
 return __bitmap_weight_and(src1, src2, nbits);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void bitmap_set(unsigned long *map, unsigned int start,
  unsigned int nbits)
{
 if (__builtin_constant_p(nbits) && nbits == 1)
  ((__builtin_constant_p(start) && __builtin_constant_p((uintptr_t)(map) != (uintptr_t)((void *)0)) && (uintptr_t)(map) != (uintptr_t)((void *)0) && __builtin_constant_p(*(const unsigned long *)(map))) ? generic___set_bit(start, map) : ___set_bit(start, map));
 else if ((__builtin_constant_p(start + nbits) && (start + nbits) <= 64 && (start + nbits) > 0))
  *map |= ((((int)(sizeof(struct { int:(-!!(__builtin_choose_expr( (sizeof(int) == sizeof(*(8 ? ((void *)((long)((start) > (start + nbits - 1)) * 0l)) : (int *)8))), (start) > (start + nbits - 1), 0))); })))) + (((~(((0UL)))) - ((((1UL))) << (start)) + 1) & (~(((0UL))) >> (64 - 1 - (start + nbits - 1)))));
 else if (__builtin_constant_p(start & (8 - 1)) &&
   (((start) & ((typeof(start))(8) - 1)) == 0) &&
   __builtin_constant_p(nbits & (8 - 1)) &&
   (((nbits) & ((typeof(nbits))(8) - 1)) == 0))
  memset((char *)map + start / 8, 0xff, nbits / 8);
 else
  __bitmap_set(map, start, nbits);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void bitmap_clear(unsigned long *map, unsigned int start,
  unsigned int nbits)
{
 if (__builtin_constant_p(nbits) && nbits == 1)
  ((__builtin_constant_p(start) && __builtin_constant_p((uintptr_t)(map) != (uintptr_t)((void *)0)) && (uintptr_t)(map) != (uintptr_t)((void *)0) && __builtin_constant_p(*(const unsigned long *)(map))) ? generic___clear_bit(start, map) : ___clear_bit(start, map));
 else if ((__builtin_constant_p(start + nbits) && (start + nbits) <= 64 && (start + nbits) > 0))
  *map &= ~((((int)(sizeof(struct { int:(-!!(__builtin_choose_expr( (sizeof(int) == sizeof(*(8 ? ((void *)((long)((start) > (start + nbits - 1)) * 0l)) : (int *)8))), (start) > (start + nbits - 1), 0))); })))) + (((~(((0UL)))) - ((((1UL))) << (start)) + 1) & (~(((0UL))) >> (64 - 1 - (start + nbits - 1)))));
 else if (__builtin_constant_p(start & (8 - 1)) &&
   (((start) & ((typeof(start))(8) - 1)) == 0) &&
   __builtin_constant_p(nbits & (8 - 1)) &&
   (((nbits) & ((typeof(nbits))(8) - 1)) == 0))
  memset((char *)map + start / 8, 0, nbits / 8);
 else
  __bitmap_clear(map, start, nbits);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void bitmap_shift_right(unsigned long *dst, const unsigned long *src,
    unsigned int shift, unsigned int nbits)
{
 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  *dst = (*src & (~0UL >> (-(nbits) & (64 - 1)))) >> shift;
 else
  __bitmap_shift_right(dst, src, shift, nbits);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void bitmap_shift_left(unsigned long *dst, const unsigned long *src,
    unsigned int shift, unsigned int nbits)
{
 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  *dst = (*src << shift) & (~0UL >> (-(nbits) & (64 - 1)));
 else
  __bitmap_shift_left(dst, src, shift, nbits);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void bitmap_replace(unsigned long *dst,
      const unsigned long *old,
      const unsigned long *new,
      const unsigned long *mask,
      unsigned int nbits)
{
 if ((__builtin_constant_p(nbits) && (nbits) <= 64 && (nbits) > 0))
  *dst = (*old & ~(*mask)) | (*new & *mask);
 else
  __bitmap_replace(dst, old, new, mask, nbits);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void bitmap_next_set_region(unsigned long *bitmap,
       unsigned int *rs, unsigned int *re,
       unsigned int end)
{
 *rs = find_next_bit(bitmap, end, *rs);
 *re = find_next_zero_bit(bitmap, end, *rs + 1);
}
# 507 "./include/linux/bitmap.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void bitmap_release_region(unsigned long *bitmap, unsigned int pos, int order)
{
 bitmap_clear(bitmap, pos, ((((1UL))) << (order)));
}
# 523 "./include/linux/bitmap.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int bitmap_allocate_region(unsigned long *bitmap, unsigned int pos, int order)
{
 unsigned int len = ((((1UL))) << (order));

 if (find_next_bit(bitmap, pos + len, pos) < pos + len)
  return -16;
 bitmap_set(bitmap, pos, len);
 return 0;
}
# 547 "./include/linux/bitmap.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int bitmap_find_free_region(unsigned long *bitmap, unsigned int bits, int order)
{
 unsigned int pos, end;

 for (pos = 0; (end = pos + ((((1UL))) << (order))) <= bits; pos = end) {
  if (!bitmap_allocate_region(bitmap, pos, order))
   return pos;
 }
 return -12;
}
# 601 "./include/linux/bitmap.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void bitmap_from_u64(unsigned long *dst, u64 mask)
{
 bitmap_copy_clear_tail((unsigned long *)(dst), (const unsigned long *)(&mask), (64));
}
# 614 "./include/linux/bitmap.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long bitmap_get_value8(const unsigned long *map,
           unsigned long start)
{
 const size_t index = ((start) / 64);
 const unsigned long offset = start % 64;

 return (map[index] >> offset) & 0xFF;
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void bitmap_set_value8(unsigned long *map, unsigned long value,
         unsigned long start)
{
 const size_t index = ((start) / 64);
 const unsigned long offset = start % 64;

 map[index] &= ~(0xFFUL << offset);
 map[index] |= value << offset;
}
# 13 "./include/linux/cpumask.h" 2

# 1 "./include/linux/bug.h" 1




# 1 "./arch/x86/include/asm/bug.h" 1





# 1 "./include/linux/instrumentation.h" 1
# 7 "./arch/x86/include/asm/bug.h" 2
# 87 "./arch/x86/include/asm/bug.h"
# 1 "./include/asm-generic/bug.h" 1
# 24 "./include/asm-generic/bug.h"
struct warn_args;
struct pt_regs;

void __warn(const char *file, int line, void *caller, unsigned taint,
     struct pt_regs *regs, struct warn_args *args);




struct bug_entry {



 signed int bug_addr_disp;





 signed int file_disp;

 unsigned short line;

 unsigned short flags;
};
# 90 "./include/asm-generic/bug.h"
extern __attribute__((__format__(printf, 4, 5)))
void warn_slowpath_fmt(const char *file, const int line, unsigned taint,
         const char *fmt, ...);
extern __attribute__((__format__(printf, 1, 2))) void __warn_printk(const char *fmt, ...);
# 88 "./arch/x86/include/asm/bug.h" 2
# 6 "./include/linux/bug.h" 2



enum bug_trap_type {
 BUG_TRAP_TYPE_NONE = 0,
 BUG_TRAP_TYPE_WARN = 1,
 BUG_TRAP_TYPE_BUG = 2,
};

struct pt_regs;
# 34 "./include/linux/bug.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int is_warning_bug(const struct bug_entry *bug)
{
 return bug->flags & (1 << 0);
}

void bug_get_file_line(struct bug_entry *bug, const char **file,
         unsigned int *line);

struct bug_entry *find_bug(unsigned long bugaddr);

enum bug_trap_type report_bug(unsigned long bug_addr, struct pt_regs *regs);


int is_valid_bugaddr(unsigned long addr);

void generic_bug_clear_once(void);
# 80 "./include/linux/bug.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__warn_unused_result__)) bool check_data_corruption(bool v) { return v; }
# 15 "./include/linux/cpumask.h" 2
# 1 "./include/linux/gfp_types.h" 1
# 16 "./include/linux/cpumask.h" 2
# 1 "./include/linux/numa.h" 1
# 26 "./include/linux/numa.h"
# 1 "./arch/x86/include/asm/sparsemem.h" 1
# 27 "./include/linux/numa.h" 2


int numa_nearest_node(int node, unsigned int state);


int memory_add_physaddr_to_nid(u64 start);



int phys_to_target_node(u64 start);


int numa_fill_memblks(u64 start, u64 end);
# 17 "./include/linux/cpumask.h" 2


typedef struct cpumask { unsigned long bits[(((64) + ((sizeof(long) * 8)) - 1) / ((sizeof(long) * 8)))]; } cpumask_t;
# 41 "./include/linux/cpumask.h"
extern unsigned int nr_cpu_ids;


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void set_nr_cpu_ids(unsigned int nr)
{



 nr_cpu_ids = nr;

}
# 125 "./include/linux/cpumask.h"
extern struct cpumask __cpu_possible_mask;
extern struct cpumask __cpu_online_mask;
extern struct cpumask __cpu_present_mask;
extern struct cpumask __cpu_active_mask;
extern struct cpumask __cpu_dying_mask;






extern atomic_t __num_online_cpus;

extern cpumask_t cpus_booted_once_mask;

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void cpu_max_bits_warn(unsigned int cpu, unsigned int bits)
{



}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned int cpumask_check(unsigned int cpu)
{
 cpu_max_bits_warn(cpu, ((unsigned int)64));
 return cpu;
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int cpumask_first(const struct cpumask *srcp)
{
 return find_first_bit(((srcp)->bits), ((unsigned int)64));
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int cpumask_first_zero(const struct cpumask *srcp)
{
 return find_first_zero_bit(((srcp)->bits), ((unsigned int)64));
}
# 183 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned int cpumask_first_and(const struct cpumask *srcp1, const struct cpumask *srcp2)
{
 return find_first_and_bit(((srcp1)->bits), ((srcp2)->bits), ((unsigned int)64));
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int cpumask_last(const struct cpumask *srcp)
{
 return find_last_bit(((srcp)->bits), ((unsigned int)64));
}
# 207 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned int cpumask_next(int n, const struct cpumask *srcp)
{

 if (n != -1)
  cpumask_check(n);
 return find_next_bit(((srcp)->bits), ((unsigned int)64), n + 1);
}
# 223 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int cpumask_next_zero(int n, const struct cpumask *srcp)
{

 if (n != -1)
  cpumask_check(n);
 return find_next_zero_bit(((srcp)->bits), ((unsigned int)64), n+1);
}
# 249 "./include/linux/cpumask.h"
unsigned int cpumask_local_spread(unsigned int i, int node);
unsigned int cpumask_any_and_distribute(const struct cpumask *src1p,
          const struct cpumask *src2p);
unsigned int cpumask_any_distribute(const struct cpumask *srcp);
# 263 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned int cpumask_next_and(int n, const struct cpumask *src1p,
       const struct cpumask *src2p)
{

 if (n != -1)
  cpumask_check(n);
 return find_next_and_bit(((src1p)->bits), ((src2p)->bits),
  ((unsigned int)64), n + 1);
}
# 302 "./include/linux/cpumask.h"
unsigned int __attribute__((__pure__)) cpumask_next_wrap(int n, const struct cpumask *mask, int start, bool wrap);
# 378 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned int cpumask_any_but(const struct cpumask *mask, unsigned int cpu)
{
 unsigned int i;

 cpumask_check(cpu);
 for ((i) = 0; (i) = find_next_bit((((mask)->bits)), (((unsigned int)64)), (i)), (i) < (((unsigned int)64)); (i)++)
  if (i != cpu)
   break;
 return i;
}
# 397 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int cpumask_nth(unsigned int cpu, const struct cpumask *srcp)
{
 return find_nth_bit(((srcp)->bits), ((unsigned int)64), cpumask_check(cpu));
}
# 410 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned int cpumask_nth_and(unsigned int cpu, const struct cpumask *srcp1,
       const struct cpumask *srcp2)
{
 return find_nth_and_bit(((srcp1)->bits), ((srcp2)->bits),
    ((unsigned int)64), cpumask_check(cpu));
}
# 426 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function))
unsigned int cpumask_nth_andnot(unsigned int cpu, const struct cpumask *srcp1,
       const struct cpumask *srcp2)
{
 return find_nth_andnot_bit(((srcp1)->bits), ((srcp2)->bits),
    ((unsigned int)64), cpumask_check(cpu));
}
# 443 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__))
unsigned int cpumask_nth_and_andnot(unsigned int cpu, const struct cpumask *srcp1,
       const struct cpumask *srcp2,
       const struct cpumask *srcp3)
{
 return find_nth_and_andnot_bit(((srcp1)->bits),
     ((srcp2)->bits),
     ((srcp3)->bits),
     ((unsigned int)64), cpumask_check(cpu));
}
# 469 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void cpumask_set_cpu(unsigned int cpu, struct cpumask *dstp)
{
 set_bit(cpumask_check(cpu), ((dstp)->bits));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void __cpumask_set_cpu(unsigned int cpu, struct cpumask *dstp)
{
 ((__builtin_constant_p(cpumask_check(cpu)) && __builtin_constant_p((uintptr_t)(((dstp)->bits)) != (uintptr_t)((void *)0)) && (uintptr_t)(((dstp)->bits)) != (uintptr_t)((void *)0) && __builtin_constant_p(*(const unsigned long *)(((dstp)->bits)))) ? generic___set_bit(cpumask_check(cpu), ((dstp)->bits)) : ___set_bit(cpumask_check(cpu), ((dstp)->bits)));
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void cpumask_clear_cpu(int cpu, struct cpumask *dstp)
{
 clear_bit(cpumask_check(cpu), ((dstp)->bits));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void __cpumask_clear_cpu(int cpu, struct cpumask *dstp)
{
 ((__builtin_constant_p(cpumask_check(cpu)) && __builtin_constant_p((uintptr_t)(((dstp)->bits)) != (uintptr_t)((void *)0)) && (uintptr_t)(((dstp)->bits)) != (uintptr_t)((void *)0) && __builtin_constant_p(*(const unsigned long *)(((dstp)->bits)))) ? generic___clear_bit(cpumask_check(cpu), ((dstp)->bits)) : ___clear_bit(cpumask_check(cpu), ((dstp)->bits)));
}
# 502 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool cpumask_test_cpu(int cpu, const struct cpumask *cpumask)
{
 return ((__builtin_constant_p(cpumask_check(cpu)) && __builtin_constant_p((uintptr_t)((((cpumask))->bits)) != (uintptr_t)((void *)0)) && (uintptr_t)((((cpumask))->bits)) != (uintptr_t)((void *)0) && __builtin_constant_p(*(const unsigned long *)((((cpumask))->bits)))) ? const_test_bit(cpumask_check(cpu), (((cpumask))->bits)) : _test_bit(cpumask_check(cpu), (((cpumask))->bits)));
}
# 516 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool cpumask_test_and_set_cpu(int cpu, struct cpumask *cpumask)
{
 return test_and_set_bit(cpumask_check(cpu), ((cpumask)->bits));
}
# 530 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool cpumask_test_and_clear_cpu(int cpu, struct cpumask *cpumask)
{
 return test_and_clear_bit(cpumask_check(cpu), ((cpumask)->bits));
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void cpumask_setall(struct cpumask *dstp)
{
 if ((__builtin_constant_p(((unsigned int)64)) && (((unsigned int)64)) <= 64 && (((unsigned int)64)) > 0)) {
  ((dstp)->bits)[0] = (~0UL >> (-(nr_cpu_ids) & (64 - 1)));
  return;
 }
 bitmap_fill(((dstp)->bits), nr_cpu_ids);
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void cpumask_clear(struct cpumask *dstp)
{
 bitmap_zero(((dstp)->bits), ((unsigned int)64));
}
# 565 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool cpumask_and(struct cpumask *dstp,
          const struct cpumask *src1p,
          const struct cpumask *src2p)
{
 return bitmap_and(((dstp)->bits), ((src1p)->bits),
           ((src2p)->bits), ((unsigned int)64));
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void cpumask_or(struct cpumask *dstp, const struct cpumask *src1p,
         const struct cpumask *src2p)
{
 bitmap_or(((dstp)->bits), ((src1p)->bits),
          ((src2p)->bits), ((unsigned int)64));
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void cpumask_xor(struct cpumask *dstp,
          const struct cpumask *src1p,
          const struct cpumask *src2p)
{
 bitmap_xor(((dstp)->bits), ((src1p)->bits),
           ((src2p)->bits), ((unsigned int)64));
}
# 608 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool cpumask_andnot(struct cpumask *dstp,
      const struct cpumask *src1p,
      const struct cpumask *src2p)
{
 return bitmap_andnot(((dstp)->bits), ((src1p)->bits),
       ((src2p)->bits), ((unsigned int)64));
}
# 623 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool cpumask_equal(const struct cpumask *src1p,
    const struct cpumask *src2p)
{
 return bitmap_equal(((src1p)->bits), ((src2p)->bits),
       ((unsigned int)64));
}
# 639 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool cpumask_or_equal(const struct cpumask *src1p,
        const struct cpumask *src2p,
        const struct cpumask *src3p)
{
 return bitmap_or_equal(((src1p)->bits), ((src2p)->bits),
          ((src3p)->bits), ((unsigned int)64));
}
# 655 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool cpumask_intersects(const struct cpumask *src1p,
         const struct cpumask *src2p)
{
 return bitmap_intersects(((src1p)->bits), ((src2p)->bits),
            ((unsigned int)64));
}
# 669 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool cpumask_subset(const struct cpumask *src1p,
     const struct cpumask *src2p)
{
 return bitmap_subset(((src1p)->bits), ((src2p)->bits),
        ((unsigned int)64));
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool cpumask_empty(const struct cpumask *srcp)
{
 return bitmap_empty(((srcp)->bits), ((unsigned int)64));
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool cpumask_full(const struct cpumask *srcp)
{
 return bitmap_full(((srcp)->bits), nr_cpu_ids);
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int cpumask_weight(const struct cpumask *srcp)
{
 return bitmap_weight(((srcp)->bits), ((unsigned int)64));
}
# 716 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int cpumask_weight_and(const struct cpumask *srcp1,
      const struct cpumask *srcp2)
{
 return bitmap_weight_and(((srcp1)->bits), ((srcp2)->bits), ((unsigned int)64));
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void cpumask_shift_right(struct cpumask *dstp,
           const struct cpumask *srcp, int n)
{
 bitmap_shift_right(((dstp)->bits), ((srcp)->bits), n,
            ((unsigned int)64));
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void cpumask_shift_left(struct cpumask *dstp,
          const struct cpumask *srcp, int n)
{
 bitmap_shift_left(((dstp)->bits), ((srcp)->bits), n,
           nr_cpu_ids);
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void cpumask_copy(struct cpumask *dstp,
    const struct cpumask *srcp)
{
 bitmap_copy(((dstp)->bits), ((srcp)->bits), ((unsigned int)64));
}
# 790 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int cpumask_parse_user(const char *buf, int len,
         struct cpumask *dstp)
{
 return bitmap_parse_user(buf, len, ((dstp)->bits), nr_cpu_ids);
}
# 804 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int cpumask_parselist_user(const char *buf, int len,
         struct cpumask *dstp)
{
 return bitmap_parselist_user(buf, len, ((dstp)->bits),
         nr_cpu_ids);
}
# 818 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int cpumask_parse(const char *buf, struct cpumask *dstp)
{
 return bitmap_parse(buf, (~0U), ((dstp)->bits), nr_cpu_ids);
}
# 830 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int cpulist_parse(const char *buf, struct cpumask *dstp)
{
 return bitmap_parselist(buf, ((dstp)->bits), nr_cpu_ids);
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int cpumask_size(void)
{
 return (((((unsigned int)64)) + ((sizeof(long) * 8)) - 1) / ((sizeof(long) * 8))) * sizeof(long);
}
# 933 "./include/linux/cpumask.h"
typedef struct cpumask cpumask_var_t[1];




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool alloc_cpumask_var(cpumask_var_t *mask, gfp_t flags)
{
 return true;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool alloc_cpumask_var_node(cpumask_var_t *mask, gfp_t flags,
       int node)
{
 return true;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool zalloc_cpumask_var(cpumask_var_t *mask, gfp_t flags)
{
 cpumask_clear(*mask);
 return true;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool zalloc_cpumask_var_node(cpumask_var_t *mask, gfp_t flags,
       int node)
{
 cpumask_clear(*mask);
 return true;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void alloc_bootmem_cpumask_var(cpumask_var_t *mask)
{
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void free_cpumask_var(cpumask_var_t mask)
{
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void free_bootmem_cpumask_var(cpumask_var_t mask)
{
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool cpumask_available(cpumask_var_t mask)
{
 return true;
}




extern const unsigned long cpu_all_bits[(((64) + ((sizeof(long) * 8)) - 1) / ((sizeof(long) * 8)))];
# 1000 "./include/linux/cpumask.h"
void init_cpu_present(const struct cpumask *src);
void init_cpu_possible(const struct cpumask *src);
void init_cpu_online(const struct cpumask *src);

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void reset_cpu_possible_mask(void)
{
 bitmap_zero(((&__cpu_possible_mask)->bits), 64);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void
set_cpu_possible(unsigned int cpu, bool possible)
{
 if (possible)
  cpumask_set_cpu(cpu, &__cpu_possible_mask);
 else
  cpumask_clear_cpu(cpu, &__cpu_possible_mask);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void
set_cpu_present(unsigned int cpu, bool present)
{
 if (present)
  cpumask_set_cpu(cpu, &__cpu_present_mask);
 else
  cpumask_clear_cpu(cpu, &__cpu_present_mask);
}

void set_cpu_online(unsigned int cpu, bool online);

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void
set_cpu_active(unsigned int cpu, bool active)
{
 if (active)
  cpumask_set_cpu(cpu, &__cpu_active_mask);
 else
  cpumask_clear_cpu(cpu, &__cpu_active_mask);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void
set_cpu_dying(unsigned int cpu, bool dying)
{
 if (dying)
  cpumask_set_cpu(cpu, &__cpu_dying_mask);
 else
  cpumask_clear_cpu(cpu, &__cpu_dying_mask);
}
# 1061 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int __check_is_bitmap(const unsigned long *bitmap)
{
 return 1;
}
# 1073 "./include/linux/cpumask.h"
extern const unsigned long
 cpu_bit_bitmap[64 +1][(((64) + ((sizeof(long) * 8)) - 1) / ((sizeof(long) * 8)))];

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) const struct cpumask *get_cpu_mask(unsigned int cpu)
{
 const unsigned long *p = cpu_bit_bitmap[1 + cpu % 64];
 p -= cpu / 64;
 return ((struct cpumask *)(1 ? (p) : (void *)sizeof(__check_is_bitmap(p))));
}
# 1094 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned int num_online_cpus(void)
{
 return raw_atomic_read(&__num_online_cpus);
}




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool cpu_online(unsigned int cpu)
{
 return cpumask_test_cpu(cpu, ((const struct cpumask *)&__cpu_online_mask));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool cpu_possible(unsigned int cpu)
{
 return cpumask_test_cpu(cpu, ((const struct cpumask *)&__cpu_possible_mask));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool cpu_present(unsigned int cpu)
{
 return cpumask_test_cpu(cpu, ((const struct cpumask *)&__cpu_present_mask));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool cpu_active(unsigned int cpu)
{
 return cpumask_test_cpu(cpu, ((const struct cpumask *)&__cpu_active_mask));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool cpu_dying(unsigned int cpu)
{
 return cpumask_test_cpu(cpu, ((const struct cpumask *)&__cpu_dying_mask));
}
# 1188 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) ssize_t
cpumap_print_to_pagebuf(bool list, char *buf, const struct cpumask *mask)
{
 return bitmap_print_to_pagebuf(list, buf, ((mask)->bits),
          nr_cpu_ids);
}
# 1211 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) ssize_t
cpumap_print_bitmask_to_buf(char *buf, const struct cpumask *mask,
  loff_t off, size_t count)
{
 return bitmap_print_bitmask_to_buf(buf, ((mask)->bits),
       nr_cpu_ids, off, count) - 1;
}
# 1233 "./include/linux/cpumask.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) ssize_t
cpumap_print_list_to_buf(char *buf, const struct cpumask *mask,
  loff_t off, size_t count)
{
 return bitmap_print_list_to_buf(buf, ((mask)->bits),
       nr_cpu_ids, off, count) - 1;
}
# 14 "./include/linux/smp.h" 2

# 1 "./include/linux/smp_types.h" 1




# 1 "./include/linux/llist.h" 1
# 56 "./include/linux/llist.h"
struct llist_head {
 struct llist_node *first;
};

struct llist_node {
 struct llist_node *next;
};
# 71 "./include/linux/llist.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void init_llist_head(struct llist_head *list)
{
 list->first = ((void *)0);
}
# 84 "./include/linux/llist.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void init_llist_node(struct llist_node *node)
{
 node->next = node;
}
# 98 "./include/linux/llist.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool llist_on_list(const struct llist_node *node)
{
 return node->next != node;
}
# 216 "./include/linux/llist.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool llist_empty(const struct llist_head *head)
{
 return ({ do { __attribute__((__noreturn__)) extern void __compiletime_assert_41(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(head->first) == sizeof(char) || sizeof(head->first) == sizeof(short) || sizeof(head->first) == sizeof(int) || sizeof(head->first) == sizeof(long)) || sizeof(head->first) == sizeof(long long))) __compiletime_assert_41(); } while (0); (*(const volatile typeof( _Generic((head->first), char: (char)0, unsigned char: (unsigned char)0, signed char: (signed char)0, unsigned short: (unsigned short)0, signed short: (signed short)0, unsigned int: (unsigned int)0, signed int: (signed int)0, unsigned long: (unsigned long)0, signed long: (signed long)0, unsigned long long: (unsigned long long)0, signed long long: (signed long long)0, default: (head->first))) *)&(head->first)); }) == ((void *)0);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) struct llist_node *llist_next(struct llist_node *node)
{
 return node->next;
}

extern bool llist_add_batch(struct llist_node *new_first,
       struct llist_node *new_last,
       struct llist_head *head);

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool __llist_add_batch(struct llist_node *new_first,
         struct llist_node *new_last,
         struct llist_head *head)
{
 new_last->next = head->first;
 head->first = new_first;
 return new_last->next == ((void *)0);
}
# 246 "./include/linux/llist.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool llist_add(struct llist_node *new, struct llist_head *head)
{
 return llist_add_batch(new, new, head);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool __llist_add(struct llist_node *new, struct llist_head *head)
{
 return __llist_add_batch(new, new, head);
}
# 264 "./include/linux/llist.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) struct llist_node *llist_del_all(struct llist_head *head)
{
 return ({ typeof(&head->first) __ai_ptr = (&head->first); do { } while (0); instrument_atomic_read_write(__ai_ptr, sizeof(*__ai_ptr)); ({ __typeof__ (*((__ai_ptr))) __ret = ((((void *)0))); switch (sizeof(*((__ai_ptr)))) { case 1: asm volatile ("" "xchg" "b %b0, %1\n" : "+q" (__ret), "+m" (*((__ai_ptr))) : : "memory", "cc"); break; case 2: asm volatile ("" "xchg" "w %w0, %1\n" : "+r" (__ret), "+m" (*((__ai_ptr))) : : "memory", "cc"); break; case 4: asm volatile ("" "xchg" "l %0, %1\n" : "+r" (__ret), "+m" (*((__ai_ptr))) : : "memory", "cc"); break; case 8: asm volatile ("" "xchg" "q %q0, %1\n" : "+r" (__ret), "+m" (*((__ai_ptr))) : : "memory", "cc"); break; default: __xchg_wrong_size(); } __ret; }); });
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) struct llist_node *__llist_del_all(struct llist_head *head)
{
 struct llist_node *first = head->first;

 head->first = ((void *)0);
 return first;
}

extern struct llist_node *llist_del_first(struct llist_head *head);
# 286 "./include/linux/llist.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) struct llist_node *llist_del_first_init(struct llist_head *head)
{
 struct llist_node *n = llist_del_first(head);

 if (n)
  init_llist_node(n);
 return n;
}

extern bool llist_del_first_this(struct llist_head *head,
     struct llist_node *this);

struct llist_node *llist_reverse_order(struct llist_node *head);
# 6 "./include/linux/smp_types.h" 2

enum {
 CSD_FLAG_LOCK = 0x01,

 IRQ_WORK_PENDING = 0x01,
 IRQ_WORK_BUSY = 0x02,
 IRQ_WORK_LAZY = 0x04,
 IRQ_WORK_HARD_IRQ = 0x08,

 IRQ_WORK_CLAIMED = (IRQ_WORK_PENDING | IRQ_WORK_BUSY),

 CSD_TYPE_ASYNC = 0x00,
 CSD_TYPE_SYNC = 0x10,
 CSD_TYPE_IRQ_WORK = 0x20,
 CSD_TYPE_TTWU = 0x30,

 CSD_FLAG_TYPE_MASK = 0xF0,
};
# 58 "./include/linux/smp_types.h"
struct __call_single_node {
 struct llist_node llist;
 union {
  unsigned int u_flags;
  atomic_t a_flags;
 };

 u16 src, dst;

};
# 16 "./include/linux/smp.h" 2

typedef void (*smp_call_func_t)(void *info);
typedef bool (*smp_cond_func_t)(int cpu, void *info);




struct __call_single_data {
 struct __call_single_node node;
 smp_call_func_t func;
 void *info;
};





typedef struct __call_single_data call_single_data_t
 __attribute__((__aligned__(sizeof(struct __call_single_data))));
# 45 "./include/linux/smp.h"
extern void __smp_call_single_queue(int cpu, struct llist_node *node);


extern unsigned int total_cpus;

int smp_call_function_single(int cpuid, smp_call_func_t func, void *info,
        int wait);

void on_each_cpu_cond_mask(smp_cond_func_t cond_func, smp_call_func_t func,
      void *info, bool wait, const struct cpumask *mask);

int smp_call_function_single_async(int cpu, call_single_data_t *csd);





void __attribute__((__noreturn__)) panic_smp_self_stop(void);
void __attribute__((__noreturn__)) nmi_panic_self_stop(struct pt_regs *regs);
void crash_smp_send_stop(void);




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void on_each_cpu(smp_call_func_t func, void *info, int wait)
{
 on_each_cpu_cond_mask(((void *)0), func, info, wait, ((const struct cpumask *)&__cpu_online_mask));
}
# 90 "./include/linux/smp.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void on_each_cpu_mask(const struct cpumask *mask,
        smp_call_func_t func, void *info, bool wait)
{
 on_each_cpu_cond_mask(((void *)0), func, info, wait, mask);
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void on_each_cpu_cond(smp_cond_func_t cond_func,
        smp_call_func_t func, void *info, bool wait)
{
 on_each_cpu_cond_mask(cond_func, func, info, wait, ((const struct cpumask *)&__cpu_online_mask));
}





# 1 "./include/linux/thread_info.h" 1
# 14 "./include/linux/thread_info.h"
# 1 "./include/linux/restart_block.h" 1
# 11 "./include/linux/restart_block.h"
struct __kernel_timespec;
struct timespec;
struct old_timespec32;
struct pollfd;

enum timespec_type {
 TT_NONE = 0,
 TT_NATIVE = 1,
 TT_COMPAT = 2,
};




struct restart_block {
 unsigned long arch_data;
 long (*fn)(struct restart_block *);
 union {

  struct {
   u32 *uaddr;
   u32 val;
   u32 flags;
   u32 bitset;
   u64 time;
   u32 *uaddr2;
  } futex;

  struct {
   clockid_t clockid;
   enum timespec_type type;
   union {
    struct __kernel_timespec *rmtp;
    struct old_timespec32 *compat_rmtp;
   };
   u64 expires;
  } nanosleep;

  struct {
   struct pollfd *ufds;
   int nfds;
   int has_timeout;
   unsigned long tv_sec;
   unsigned long tv_nsec;
  } poll;
 };
};

extern long do_no_restart_syscall(struct restart_block *parm);
# 15 "./include/linux/thread_info.h" 2
# 33 "./include/linux/thread_info.h"
enum {
 BAD_STACK = -1,
 NOT_STACK = 0,
 GOOD_FRAME,
 GOOD_STACK,
};


enum syscall_work_bit {
 SYSCALL_WORK_BIT_SECCOMP,
 SYSCALL_WORK_BIT_SYSCALL_TRACEPOINT,
 SYSCALL_WORK_BIT_SYSCALL_TRACE,
 SYSCALL_WORK_BIT_SYSCALL_EMU,
 SYSCALL_WORK_BIT_SYSCALL_AUDIT,
 SYSCALL_WORK_BIT_SYSCALL_USER_DISPATCH,
 SYSCALL_WORK_BIT_SYSCALL_EXIT_TRAP,
};
# 60 "./include/linux/thread_info.h"
# 1 "./arch/x86/include/asm/thread_info.h" 1
# 12 "./arch/x86/include/asm/thread_info.h"
# 1 "./arch/x86/include/asm/page.h" 1
# 9 "./arch/x86/include/asm/page.h"
# 1 "./arch/x86/include/asm/page_types.h" 1
# 40 "./arch/x86/include/asm/page_types.h"
# 1 "./arch/x86/include/asm/page_64_types.h" 1





# 1 "./arch/x86/include/asm/kaslr.h" 1




unsigned long kaslr_get_random_long(const char *purpose);


void kernel_randomize_memory(void);
void init_trampoline_kaslr(void);
# 7 "./arch/x86/include/asm/page_64_types.h" 2
# 41 "./arch/x86/include/asm/page_types.h" 2
# 56 "./arch/x86/include/asm/page_types.h"
extern int devmem_is_allowed(unsigned long pagenr);

extern unsigned long max_low_pfn_mapped;
extern unsigned long max_pfn_mapped;

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) phys_addr_t get_max_mapped(void)
{
 return (phys_addr_t)max_pfn_mapped << 12;
}

bool pfn_range_is_mapped(unsigned long start_pfn, unsigned long end_pfn);

extern void initmem_init(void);
# 10 "./arch/x86/include/asm/page.h" 2


# 1 "./arch/x86/include/asm/page_64.h" 1
# 14 "./arch/x86/include/asm/page_64.h"
extern unsigned long max_pfn;
extern unsigned long phys_base;

extern unsigned long page_offset_base;
extern unsigned long vmalloc_base;
extern unsigned long vmemmap_base;

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long __phys_addr_nodebug(unsigned long x)
{
 unsigned long y = x - (0xffffffff80000000UL);


 x = y + ((x > y) ? phys_base : ((0xffffffff80000000UL) - ((unsigned long)page_offset_base)));

 return x;
}
# 42 "./arch/x86/include/asm/page_64.h"
void clear_page_orig(void *page);
void clear_page_rep(void *page);
void clear_page_erms(void *page);

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void clear_page(void *page)
{




 kmsan_unpoison_memory(page, ((1UL) << 12));
 asm __inline volatile ("# ALT: oldinstr2\n" "661:\n\t" "call %P[old]" "\n662:\n" "# ALT: padding2\n" ".skip -((" "((" "665""1""f-""664""1""f" ") ^ (((" "665""1""f-""664""1""f" ") ^ (" "665""2""f-""664""2""f" ")) & -(-((" "665""1""f-""664""1""f" ") < (" "665""2""f-""664""2""f" ")))))" " - (" "662b-661b" ")) > 0) * " "(" "((" "665""1""f-""664""1""f" ") ^ (((" "665""1""f-""664""1""f" ") ^ (" "665""2""f-""664""2""f" ")) & -(-((" "665""1""f-""664""1""f" ") < (" "665""2""f-""664""2""f" ")))))" " - (" "662b-661b" ")), 0x90\n" "663" ":\n" ".pushsection .altinstructions,\"a\"\n" " .long 661b - .\n" " .long " "664""1""f - .\n" " .4byte " "( 3*32+16)" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""1""f-""664""1""f" "\n" " .long 661b - .\n" " .long " "664""2""f - .\n" " .4byte " "( 9*32+ 9)" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""2""f-""664""2""f" "\n" ".popsection\n" ".pushsection .altinstr_replacement, \"ax\"\n" "# ALT: replacement " "1" "\n" "664""1"":\n\t" "call %P[new1]" "\n" "665""1" ":\n" "# ALT: replacement " "2" "\n" "664""2"":\n\t" "call %P[new2]" "\n" "665""2" ":\n" ".popsection\n" : "=D" (page), "+r" (current_stack_pointer) : [old] "i" (clear_page_orig), [new1] "i" (clear_page_rep), [new2] "i" (clear_page_erms), "0" (page) : "cc", "memory", "rax", "rcx")




                                     ;
}

void copy_page(void *to, void *from);
# 82 "./arch/x86/include/asm/page_64.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long task_size_max(void)
{
 unsigned long ret;

 asm __inline volatile ("# ALT: oldnstr\n" "661:\n\t" "movq %[small],%0" "\n662:\n" "# ALT: padding\n" ".skip -(((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")) > 0) * " "((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")),0x90\n" "663" ":\n" ".pushsection .altinstructions,\"a\"\n" " .long 661b - .\n" " .long " "664""1""f - .\n" " .4byte " "(16*32+16)" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""1""f-""664""1""f" "\n" ".popsection\n" ".pushsection .altinstr_replacement, \"ax\"\n" "# ALT: replacement " "1" "\n" "664""1"":\n\t" "movq %[large],%0" "\n" "665""1" ":\n" ".popsection\n" : "=r" (ret) : "i" (0), [small] "i" ((1ul << 47)-((1UL) << 12)), [large] "i" ((1ul << 56)-((1UL) << 12)))



                                       ;

 return ret;
}
# 13 "./arch/x86/include/asm/page.h" 2






struct page;

# 1 "./include/linux/range.h" 1





struct range {
 u64 start;
 u64 end;
};

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) u64 range_len(const struct range *range)
{
 return range->end - range->start + 1;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool range_contains(struct range *r1, struct range *r2)
{
 return r1->start <= r2->start && r1->end >= r2->end;
}

int add_range(struct range *range, int az, int nr_range,
  u64 start, u64 end);


int add_range_with_merge(struct range *range, int az, int nr_range,
    u64 start, u64 end);

void subtract_range(struct range *range, int az, u64 start, u64 end);

int clean_sort_range(struct range *range, int az);

void sort_range(struct range *range, int nr_range);
# 22 "./arch/x86/include/asm/page.h" 2
extern struct range pfn_mapped[];
extern int nr_pfn_mapped;

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void clear_user_page(void *page, unsigned long vaddr,
       struct page *pg)
{
 clear_page(page);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void copy_user_page(void *to, void *from, unsigned long vaddr,
      struct page *topage)
{
 copy_page(to, from);
}
# 69 "./arch/x86/include/asm/page.h"
extern bool __virt_addr_valid(unsigned long kaddr);


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void *pfn_to_kaddr(unsigned long pfn)
{
 return ((void *)((unsigned long)(pfn << 12)+((unsigned long)page_offset_base)));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) u64 __canonical_address(u64 vaddr, u8 vaddr_bits)
{
 return ((s64)vaddr << (64 - vaddr_bits)) >> (64 - vaddr_bits);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) u64 __is_canonical_address(u64 vaddr, u8 vaddr_bits)
{
 return __canonical_address(vaddr, vaddr_bits) == vaddr;
}



# 1 "./include/asm-generic/memory_model.h" 1




# 1 "./include/linux/pfn.h" 1
# 13 "./include/linux/pfn.h"
typedef struct {
 u64 val;
} pfn_t;
# 6 "./include/asm-generic/memory_model.h" 2
# 90 "./arch/x86/include/asm/page.h" 2
# 1 "./include/asm-generic/getorder.h" 1
# 29 "./include/asm-generic/getorder.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __attribute__((__const__)) int get_order(unsigned long size)
{
 if (__builtin_constant_p(size)) {
  if (!size)
   return 64 - 12;

  if (size < (1UL << 12))
   return 0;

  return ( __builtin_constant_p((size) - 1) ? (((size) - 1) < 2 ? 0 : 63 - __builtin_clzll((size) - 1)) : (sizeof((size) - 1) <= 4) ? __ilog2_u32((size) - 1) : __ilog2_u64((size) - 1) ) - 12 + 1;
 }

 size--;
 size >>= 12;



 return fls64(size);

}
# 91 "./arch/x86/include/asm/page.h" 2
# 13 "./arch/x86/include/asm/thread_info.h" 2

# 1 "./arch/x86/include/generated/uapi/asm/types.h" 1
# 15 "./arch/x86/include/asm/thread_info.h" 2
# 52 "./arch/x86/include/asm/thread_info.h"
struct task_struct;
# 1 "./arch/x86/include/asm/cpufeature.h" 1




# 1 "./arch/x86/include/asm/processor.h" 1







struct task_struct;
struct mm_struct;
struct io_bitmap;
struct vm86;

# 1 "./arch/x86/include/asm/math_emu.h" 1




# 1 "./arch/x86/include/asm/ptrace.h" 1






# 1 "./arch/x86/include/uapi/asm/ptrace.h" 1





# 1 "./arch/x86/include/uapi/asm/ptrace-abi.h" 1
# 7 "./arch/x86/include/uapi/asm/ptrace.h" 2
# 8 "./arch/x86/include/asm/ptrace.h" 2
# 59 "./arch/x86/include/asm/ptrace.h"
struct pt_regs {




 unsigned long r15;
 unsigned long r14;
 unsigned long r13;
 unsigned long r12;
 unsigned long bp;
 unsigned long bx;

 unsigned long r11;
 unsigned long r10;
 unsigned long r9;
 unsigned long r8;
 unsigned long ax;
 unsigned long cx;
 unsigned long dx;
 unsigned long si;
 unsigned long di;




 unsigned long orig_ax;

 unsigned long ip;
 unsigned long cs;
 unsigned long flags;
 unsigned long sp;
 unsigned long ss;

};




# 1 "./arch/x86/include/asm/paravirt_types.h" 1
# 10 "./arch/x86/include/asm/paravirt_types.h"
# 1 "./arch/x86/include/asm/desc_defs.h" 1
# 66 "./arch/x86/include/asm/desc_defs.h"
struct desc_struct {
 u16 limit0;
 u16 base0;
 u16 base1: 8, type: 4, s: 1, dpl: 2, p: 1;
 u16 limit1: 4, avl: 1, l: 1, d: 1, g: 1, base2: 8;
} __attribute__((packed));
# 90 "./arch/x86/include/asm/desc_defs.h"
enum {
 GATE_INTERRUPT = 0xE,
 GATE_TRAP = 0xF,
 GATE_CALL = 0xC,
 GATE_TASK = 0x5,
};

enum {
 DESC_TSS = 0x9,
 DESC_LDT = 0x2,
 DESCTYPE_S = 0x10,
};


struct ldttss_desc {
 u16 limit0;
 u16 base0;

 u16 base1 : 8, type : 5, dpl : 2, p : 1;
 u16 limit1 : 4, zero0 : 3, g : 1, base2 : 8;

 u32 base3;
 u32 zero1;

} __attribute__((packed));

typedef struct ldttss_desc ldt_desc;
typedef struct ldttss_desc tss_desc;

struct idt_bits {
 u16 ist : 3,
   zero : 5,
   type : 5,
   dpl : 2,
   p : 1;
} __attribute__((packed));

struct idt_data {
 unsigned int vector;
 unsigned int segment;
 struct idt_bits bits;
 const void *addr;
};

struct gate_struct {
 u16 offset_low;
 u16 segment;
 struct idt_bits bits;
 u16 offset_middle;

 u32 offset_high;
 u32 reserved;

} __attribute__((packed));

typedef struct gate_struct gate_desc;


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long gate_offset(const gate_desc *g)
{

 return g->offset_low | ((unsigned long)g->offset_middle << 16) |
  ((unsigned long) g->offset_high << 32);



}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long gate_segment(const gate_desc *g)
{
 return g->segment;
}


struct desc_ptr {
 unsigned short size;
 unsigned long address;
} __attribute__((packed)) ;
# 11 "./arch/x86/include/asm/paravirt_types.h" 2
# 1 "./arch/x86/include/asm/pgtable_types.h" 1
# 164 "./arch/x86/include/asm/pgtable_types.h"
enum page_cache_mode {
 _PAGE_CACHE_MODE_WB = 0,
 _PAGE_CACHE_MODE_WC = 1,
 _PAGE_CACHE_MODE_UC_MINUS = 2,
 _PAGE_CACHE_MODE_UC = 3,
 _PAGE_CACHE_MODE_WT = 4,
 _PAGE_CACHE_MODE_WP = 5,

 _PAGE_CACHE_MODE_NUM = 8
};
# 277 "./arch/x86/include/asm/pgtable_types.h"
# 1 "./arch/x86/include/asm/pgtable_64_types.h" 1
# 14 "./arch/x86/include/asm/pgtable_64_types.h"
typedef unsigned long pteval_t;
typedef unsigned long pmdval_t;
typedef unsigned long pudval_t;
typedef unsigned long p4dval_t;
typedef unsigned long pgdval_t;
typedef unsigned long pgprotval_t;

typedef struct { pteval_t pte; } pte_t;
typedef struct { pmdval_t pmd; } pmd_t;


extern unsigned int __pgtable_l5_enabled;
# 44 "./arch/x86/include/asm/pgtable_64_types.h"
extern unsigned int pgdir_shift;
extern unsigned int ptrs_per_p4d;
# 278 "./arch/x86/include/asm/pgtable_types.h" 2
# 293 "./arch/x86/include/asm/pgtable_types.h"
typedef struct pgprot { pgprotval_t pgprot; } pgprot_t;

typedef struct { pgdval_t pgd; } pgd_t;

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pgprot_t pgprot_nx(pgprot_t prot)
{
 return ((pgprot_t) { (((prot).pgprot) | (((pteval_t)(1)) << 63)) } );
}
# 326 "./arch/x86/include/asm/pgtable_types.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pgd_t native_make_pgd(pgdval_t val)
{
 return (pgd_t) { val & (~0ULL) };
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pgdval_t native_pgd_val(pgd_t pgd)
{
 return pgd.pgd & (~0ULL);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pgdval_t pgd_flags(pgd_t pgd)
{
 return native_pgd_val(pgd) & (~((pteval_t)(((signed long)(~(((1UL) << 12)-1))) & ((phys_addr_t)((1ULL << 52) - 1)))));
}


typedef struct { p4dval_t p4d; } p4d_t;

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) p4d_t native_make_p4d(pudval_t val)
{
 return (p4d_t) { val };
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) p4dval_t native_p4d_val(p4d_t p4d)
{
 return p4d.p4d;
}
# 368 "./arch/x86/include/asm/pgtable_types.h"
typedef struct { pudval_t pud; } pud_t;

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pud_t native_make_pud(pmdval_t val)
{
 return (pud_t) { val };
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pudval_t native_pud_val(pud_t pud)
{
 return pud.pud;
}
# 394 "./arch/x86/include/asm/pgtable_types.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pmd_t native_make_pmd(pmdval_t val)
{
 return (pmd_t) { .pmd = val };
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pmdval_t native_pmd_val(pmd_t pmd)
{
 return pmd.pmd;
}
# 417 "./arch/x86/include/asm/pgtable_types.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) p4dval_t p4d_pfn_mask(p4d_t p4d)
{

 return ((pteval_t)(((signed long)(~(((1UL) << 12)-1))) & ((phys_addr_t)((1ULL << 52) - 1))));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) p4dval_t p4d_flags_mask(p4d_t p4d)
{
 return ~p4d_pfn_mask(p4d);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) p4dval_t p4d_flags(p4d_t p4d)
{
 return native_p4d_val(p4d) & p4d_flags_mask(p4d);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pudval_t pud_pfn_mask(pud_t pud)
{
 if (native_pud_val(pud) & (((pteval_t)(1)) << 7))
  return (((signed long)(~(((1UL) << 30) - 1))) & ((phys_addr_t)((1ULL << 52) - 1)));
 else
  return ((pteval_t)(((signed long)(~(((1UL) << 12)-1))) & ((phys_addr_t)((1ULL << 52) - 1))));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pudval_t pud_flags_mask(pud_t pud)
{
 return ~pud_pfn_mask(pud);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pudval_t pud_flags(pud_t pud)
{
 return native_pud_val(pud) & pud_flags_mask(pud);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pmdval_t pmd_pfn_mask(pmd_t pmd)
{
 if (native_pmd_val(pmd) & (((pteval_t)(1)) << 7))
  return (((signed long)(~(((1UL) << 21) - 1))) & ((phys_addr_t)((1ULL << 52) - 1)));
 else
  return ((pteval_t)(((signed long)(~(((1UL) << 12)-1))) & ((phys_addr_t)((1ULL << 52) - 1))));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pmdval_t pmd_flags_mask(pmd_t pmd)
{
 return ~pmd_pfn_mask(pmd);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pmdval_t pmd_flags(pmd_t pmd)
{
 return native_pmd_val(pmd) & pmd_flags_mask(pmd);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pte_t native_make_pte(pteval_t val)
{
 return (pte_t) { .pte = val };
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pteval_t native_pte_val(pte_t pte)
{
 return pte.pte;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pteval_t pte_flags(pte_t pte)
{
 return native_pte_val(pte) & (~((pteval_t)(((signed long)(~(((1UL) << 12)-1))) & ((phys_addr_t)((1ULL << 52) - 1)))));
}
# 493 "./arch/x86/include/asm/pgtable_types.h"
unsigned long cachemode2protval(enum page_cache_mode pcm);

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pgprotval_t protval_4k_2_large(pgprotval_t val)
{
 return (val & ~((((pteval_t)(1)) << 7) | (((pteval_t)(1)) << 12))) |
  ((val & (((pteval_t)(1)) << 7)) << (12 - 7));
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pgprot_t pgprot_4k_2_large(pgprot_t pgprot)
{
 return ((pgprot_t) { (protval_4k_2_large(((pgprot).pgprot))) } );
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pgprotval_t protval_large_2_4k(pgprotval_t val)
{
 return (val & ~((((pteval_t)(1)) << 7) | (((pteval_t)(1)) << 12))) |
  ((val & (((pteval_t)(1)) << 12)) >>
   (12 - 7));
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) pgprot_t pgprot_large_2_4k(pgprot_t pgprot)
{
 return ((pgprot_t) { (protval_large_2_4k(((pgprot).pgprot))) } );
}


typedef struct page *pgtable_t;

extern pteval_t __supported_pte_mask;
extern pteval_t __default_kernel_pte_mask;
extern void set_nx(void);
extern int nx_enabled;


extern pgprot_t pgprot_writecombine(pgprot_t prot);


extern pgprot_t pgprot_writethrough(pgprot_t prot);





struct file;
pgprot_t phys_mem_access_prot(struct file *file, unsigned long pfn,
                              unsigned long size, pgprot_t vma_prot);


void set_pte_vaddr(unsigned long vaddr, pte_t pte);







enum pg_level {
 PG_LEVEL_NONE,
 PG_LEVEL_4K,
 PG_LEVEL_2M,
 PG_LEVEL_1G,
 PG_LEVEL_512G,
 PG_LEVEL_NUM
};


extern void update_page_count(int level, unsigned long pages);
# 567 "./arch/x86/include/asm/pgtable_types.h"
extern pte_t *lookup_address(unsigned long address, unsigned int *level);
extern pte_t *lookup_address_in_pgd(pgd_t *pgd, unsigned long address,
        unsigned int *level);
pte_t *lookup_address_in_pgd_attr(pgd_t *pgd, unsigned long address,
      unsigned int *level, bool *nx, bool *rw);
extern pmd_t *lookup_pmd_address(unsigned long address);
extern phys_addr_t slow_virt_to_phys(void *__address);
extern int __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep"))) kernel_map_pages_in_pgd(pgd_t *pgd, u64 pfn,
       unsigned long address,
       unsigned numpages,
       unsigned long page_flags);
extern int __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep"))) kernel_unmap_pages_in_pgd(pgd_t *pgd, unsigned long address,
         unsigned long numpages);
# 12 "./arch/x86/include/asm/paravirt_types.h" 2


struct page;
struct thread_struct;
struct desc_ptr;
struct tss_struct;
struct mm_struct;
struct desc_struct;
struct task_struct;
struct cpumask;
struct flush_tlb_info;
struct mmu_gather;
struct vm_area_struct;





struct paravirt_callee_save {
 void *func;
};


struct pv_info {




 const char *name;
};
# 52 "./arch/x86/include/asm/paravirt_types.h"
struct pv_cpu_ops {

 void (*io_delay)(void);
# 111 "./arch/x86/include/asm/paravirt_types.h"
} ;

struct pv_irq_ops {
# 129 "./arch/x86/include/asm/paravirt_types.h"
} ;

struct pv_mmu_ops {

 void (*flush_tlb_user)(void);
 void (*flush_tlb_kernel)(void);
 void (*flush_tlb_one_user)(unsigned long addr);
 void (*flush_tlb_multi)(const struct cpumask *cpus,
    const struct flush_tlb_info *info);

 void (*tlb_remove_table)(struct mmu_gather *tlb, void *table);


 void (*exit_mmap)(struct mm_struct *mm);
 void (*notify_page_enc_status_changed)(unsigned long pfn, int npages, bool enc);
# 213 "./arch/x86/include/asm/paravirt_types.h"
} ;

struct arch_spinlock;




struct qspinlock;

struct pv_lock_ops {
 void (*queued_spin_lock_slowpath)(struct qspinlock *lock, u32 val);
 struct paravirt_callee_save queued_spin_unlock;

 void (*wait)(u8 *ptr, u8 val);
 void (*kick)(int cpu);

 struct paravirt_callee_save vcpu_is_preempted;
} ;




struct paravirt_patch_template {
 struct pv_cpu_ops cpu;
 struct pv_irq_ops irq;
 struct pv_mmu_ops mmu;
 struct pv_lock_ops lock;
} ;

extern struct pv_info pv_info;
extern struct paravirt_patch_template pv_ops;



int paravirt_disable_iospace(void);
# 513 "./arch/x86/include/asm/paravirt_types.h"
unsigned long paravirt_ret0(void);
# 98 "./arch/x86/include/asm/ptrace.h" 2


# 1 "./arch/x86/include/asm/proto.h" 1




# 1 "./arch/x86/include/uapi/asm/ldt.h" 1
# 21 "./arch/x86/include/uapi/asm/ldt.h"
struct user_desc {
 unsigned int entry_number;
 unsigned int base_addr;
 unsigned int limit;
 unsigned int seg_32bit:1;
 unsigned int contents:2;
 unsigned int read_exec_only:1;
 unsigned int limit_in_pages:1;
 unsigned int seg_not_present:1;
 unsigned int useable:1;
# 39 "./arch/x86/include/uapi/asm/ldt.h"
 unsigned int lm:1;

};
# 6 "./arch/x86/include/asm/proto.h" 2

struct task_struct;



void syscall_init(void);


void entry_SYSCALL_64(void);
void entry_SYSCALL_64_safe_stack(void);
void entry_SYSRETQ_unsafe_stack(void);
void entry_SYSRETQ_end(void);
long do_arch_prctl_64(struct task_struct *task, int option, unsigned long arg2);
# 29 "./arch/x86/include/asm/proto.h"
void entry_SYSENTER_compat(void);
void __end_entry_SYSENTER_compat(void);
void entry_SYSCALL_compat(void);
void entry_SYSCALL_compat_safe_stack(void);
void entry_SYSRETL_compat_unsafe_stack(void);
void entry_SYSRETL_compat_end(void);





void x86_configure_nx(void);

extern int reboot_force;

long do_arch_prctl_common(int option, unsigned long arg2);
# 101 "./arch/x86/include/asm/ptrace.h" 2

struct cpuinfo_x86;
struct task_struct;

extern unsigned long profile_pc(struct pt_regs *regs);

extern unsigned long
convert_ip_to_linear(struct task_struct *child, struct pt_regs *regs);
extern void send_sigtrap(struct pt_regs *regs, int error_code, int si_code);


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long regs_return_value(struct pt_regs *regs)
{
 return regs->ax;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void regs_set_return_value(struct pt_regs *regs, unsigned long rc)
{
 regs->ax = rc;
}
# 131 "./arch/x86/include/asm/ptrace.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) int user_mode(struct pt_regs *regs)
{



 return !!(regs->cs & 3);

}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) int v8086_mode(struct pt_regs *regs)
{



 return 0;

}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool user_64bit_mode(struct pt_regs *regs)
{






 return regs->cs == (6*8 + 3);







}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool any_64bit_mode(struct pt_regs *regs)
{

 return !user_mode(regs) || user_64bit_mode(regs);



}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool ip_within_syscall_gap(struct pt_regs *regs)
{
 bool ret = (regs->ip >= (unsigned long)entry_SYSCALL_64 &&
      regs->ip < (unsigned long)entry_SYSCALL_64_safe_stack);

 ret = ret || (regs->ip >= (unsigned long)entry_SYSRETQ_unsafe_stack &&
        regs->ip < (unsigned long)entry_SYSRETQ_end);

 ret = ret || (regs->ip >= (unsigned long)entry_SYSCALL_compat &&
        regs->ip < (unsigned long)entry_SYSCALL_compat_safe_stack);
 ret = ret || (regs->ip >= (unsigned long)entry_SYSRETL_compat_unsafe_stack &&
        regs->ip < (unsigned long)entry_SYSRETL_compat_end);


 return ret;
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long kernel_stack_pointer(struct pt_regs *regs)
{
 return regs->sp;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long instruction_pointer(struct pt_regs *regs)
{
 return regs->ip;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void instruction_pointer_set(struct pt_regs *regs,
  unsigned long val)
{
 regs->ip = val;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long frame_pointer(struct pt_regs *regs)
{
 return regs->bp;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long user_stack_pointer(struct pt_regs *regs)
{
 return regs->sp;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void user_stack_pointer_set(struct pt_regs *regs,
  unsigned long val)
{
 regs->sp = val;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool regs_irqs_disabled(struct pt_regs *regs)
{
 return !(regs->flags & (((1UL)) << (9)));
}


extern int regs_query_register_offset(const char *name);
extern const char *regs_query_register_name(unsigned int offset);
# 253 "./arch/x86/include/asm/ptrace.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long regs_get_register(struct pt_regs *regs,
           unsigned int offset)
{
 if (__builtin_expect(!!(offset > (__builtin_offsetof(struct pt_regs, ss))), 0))
  return 0;
# 270 "./arch/x86/include/asm/ptrace.h"
 return *(unsigned long *)((unsigned long)regs + offset);
}
# 281 "./arch/x86/include/asm/ptrace.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int regs_within_kernel_stack(struct pt_regs *regs,
        unsigned long addr)
{
 return ((addr & ~((((1UL) << 12) << (2 + 0)) - 1)) == (regs->sp & ~((((1UL) << 12) << (2 + 0)) - 1)));
}
# 296 "./arch/x86/include/asm/ptrace.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long *regs_get_kernel_stack_nth_addr(struct pt_regs *regs, unsigned int n)
{
 unsigned long *addr = (unsigned long *)regs->sp;

 addr += n;
 if (regs_within_kernel_stack(regs, (unsigned long)addr))
  return addr;
 else
  return ((void *)0);
}


extern long copy_from_kernel_nofault(void *dst, const void *src, size_t size);
# 319 "./arch/x86/include/asm/ptrace.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long regs_get_kernel_stack_nth(struct pt_regs *regs,
            unsigned int n)
{
 unsigned long *addr;
 unsigned long val;
 long ret;

 addr = regs_get_kernel_stack_nth_addr(regs, n);
 if (addr) {
  ret = copy_from_kernel_nofault(&val, addr, sizeof(val));
  if (!ret)
   return val;
 }
 return 0;
}
# 346 "./arch/x86/include/asm/ptrace.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long regs_get_kernel_argument(struct pt_regs *regs,
           unsigned int n)
{
 static const unsigned int argument_offs[] = {






  __builtin_offsetof(struct pt_regs, di),
  __builtin_offsetof(struct pt_regs, si),
  __builtin_offsetof(struct pt_regs, dx),
  __builtin_offsetof(struct pt_regs, cx),
  __builtin_offsetof(struct pt_regs, r8),
  __builtin_offsetof(struct pt_regs, r9),


 };

 if (n >= 6) {
  n -= 6 - 1;
  return regs_get_kernel_stack_nth(regs, n);
 } else
  return regs_get_register(regs, argument_offs[n]);
}
# 382 "./arch/x86/include/asm/ptrace.h"
struct user_desc;
extern int do_get_thread_area(struct task_struct *p, int idx,
         struct user_desc *info);
extern int do_set_thread_area(struct task_struct *p, int idx,
         struct user_desc *info, int can_allocate);
# 6 "./arch/x86/include/asm/math_emu.h" 2





struct math_emu_info {
 long ___orig_eip;
 struct pt_regs *regs;
};
# 14 "./arch/x86/include/asm/processor.h" 2

# 1 "./arch/x86/include/generated/uapi/asm/types.h" 1
# 16 "./arch/x86/include/asm/processor.h" 2
# 1 "./arch/x86/include/uapi/asm/sigcontext.h" 1
# 40 "./arch/x86/include/uapi/asm/sigcontext.h"
struct _fpx_sw_bytes {




 __u32 magic1;
# 54 "./arch/x86/include/uapi/asm/sigcontext.h"
 __u32 extended_size;





 __u64 xfeatures;





 __u32 xstate_size;


 __u32 padding[7];
};
# 85 "./arch/x86/include/uapi/asm/sigcontext.h"
struct _fpreg {
 __u16 significand[4];
 __u16 exponent;
};


struct _fpxreg {
 __u16 significand[4];
 __u16 exponent;
 __u16 padding[3];
};


struct _xmmreg {
 __u32 element[4];
};






struct _fpstate_32 {

 __u32 cw;
 __u32 sw;
 __u32 tag;
 __u32 ipoff;
 __u32 cssel;
 __u32 dataoff;
 __u32 datasel;
 struct _fpreg _st[8];
 __u16 status;
 __u16 magic;



 __u32 _fxsr_env[6];
 __u32 mxcsr;
 __u32 reserved;
 struct _fpxreg _fxsr_st[8];
 struct _xmmreg _xmm[8];
 union {
  __u32 padding1[44];
  __u32 padding[44];
 };

 union {
  __u32 padding2[12];
  struct _fpx_sw_bytes sw_reserved;
 };
};
# 149 "./arch/x86/include/uapi/asm/sigcontext.h"
struct _fpstate_64 {
 __u16 cwd;
 __u16 swd;

 __u16 twd;
 __u16 fop;
 __u64 rip;
 __u64 rdp;
 __u32 mxcsr;
 __u32 mxcsr_mask;
 __u32 st_space[32];
 __u32 xmm_space[64];
 __u32 reserved2[12];
 union {
  __u32 reserved3[12];
  struct _fpx_sw_bytes sw_reserved;
 };
};







struct _header {
 __u64 xfeatures;
 __u64 reserved1[2];
 __u64 reserved2[5];
};

struct _ymmh_state {

 __u32 ymmh_space[64];
};
# 192 "./arch/x86/include/uapi/asm/sigcontext.h"
struct _xstate {
 struct _fpstate_64 fpstate;
 struct _header xstate_hdr;
 struct _ymmh_state ymmh;

};




struct sigcontext_32 {
 __u16 gs, __gsh;
 __u16 fs, __fsh;
 __u16 es, __esh;
 __u16 ds, __dsh;
 __u32 di;
 __u32 si;
 __u32 bp;
 __u32 sp;
 __u32 bx;
 __u32 dx;
 __u32 cx;
 __u32 ax;
 __u32 trapno;
 __u32 err;
 __u32 ip;
 __u16 cs, __csh;
 __u32 flags;
 __u32 sp_at_signal;
 __u16 ss, __ssh;
# 230 "./arch/x86/include/uapi/asm/sigcontext.h"
 __u32 fpstate;
 __u32 oldmask;
 __u32 cr2;
};




struct sigcontext_64 {
 __u64 r8;
 __u64 r9;
 __u64 r10;
 __u64 r11;
 __u64 r12;
 __u64 r13;
 __u64 r14;
 __u64 r15;
 __u64 di;
 __u64 si;
 __u64 bp;
 __u64 bx;
 __u64 dx;
 __u64 ax;
 __u64 cx;
 __u64 sp;
 __u64 ip;
 __u64 flags;
 __u16 cs;
 __u16 gs;
 __u16 fs;
 __u16 ss;
 __u64 err;
 __u64 trapno;
 __u64 oldmask;
 __u64 cr2;
# 273 "./arch/x86/include/uapi/asm/sigcontext.h"
 __u64 fpstate;
 __u64 reserved1[8];
};
# 17 "./arch/x86/include/asm/processor.h" 2


# 1 "./arch/x86/include/asm/cpuid.h" 1
# 9 "./arch/x86/include/asm/cpuid.h"
# 1 "./arch/x86/include/asm/string.h" 1
# 10 "./arch/x86/include/asm/cpuid.h" 2

struct cpuid_regs {
 u32 eax, ebx, ecx, edx;
};

enum cpuid_regs_idx {
 CPUID_EAX = 0,
 CPUID_EBX,
 CPUID_ECX,
 CPUID_EDX,
};




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int have_cpuid_p(void)
{
 return 1;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void native_cpuid(unsigned int *eax, unsigned int *ebx,
    unsigned int *ecx, unsigned int *edx)
{

 asm volatile("cpuid"
     : "=a" (*eax),
       "=b" (*ebx),
       "=c" (*ecx),
       "=d" (*edx)
     : "0" (*eax), "2" (*ecx)
     : "memory");
}
# 56 "./arch/x86/include/asm/cpuid.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int native_cpuid_eax(unsigned int op) { unsigned int eax = op, ebx, ecx = 0, edx; native_cpuid(&eax, &ebx, &ecx, &edx); return eax; }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int native_cpuid_ebx(unsigned int op) { unsigned int eax = op, ebx, ecx = 0, edx; native_cpuid(&eax, &ebx, &ecx, &edx); return ebx; }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int native_cpuid_ecx(unsigned int op) { unsigned int eax = op, ebx, ecx = 0, edx; native_cpuid(&eax, &ebx, &ecx, &edx); return ecx; }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int native_cpuid_edx(unsigned int op) { unsigned int eax = op, ebx, ecx = 0, edx; native_cpuid(&eax, &ebx, &ecx, &edx); return edx; }
# 72 "./arch/x86/include/asm/cpuid.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void cpuid(unsigned int op,
    unsigned int *eax, unsigned int *ebx,
    unsigned int *ecx, unsigned int *edx)
{
 *eax = op;
 *ecx = 0;
 native_cpuid(eax, ebx, ecx, edx);
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void cpuid_count(unsigned int op, int count,
          unsigned int *eax, unsigned int *ebx,
          unsigned int *ecx, unsigned int *edx)
{
 *eax = op;
 *ecx = count;
 native_cpuid(eax, ebx, ecx, edx);
}




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int cpuid_eax(unsigned int op)
{
 unsigned int eax, ebx, ecx, edx;

 cpuid(op, &eax, &ebx, &ecx, &edx);

 return eax;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int cpuid_ebx(unsigned int op)
{
 unsigned int eax, ebx, ecx, edx;

 cpuid(op, &eax, &ebx, &ecx, &edx);

 return ebx;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int cpuid_ecx(unsigned int op)
{
 unsigned int eax, ebx, ecx, edx;

 cpuid(op, &eax, &ebx, &ecx, &edx);

 return ecx;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned int cpuid_edx(unsigned int op)
{
 unsigned int eax, ebx, ecx, edx;

 cpuid(op, &eax, &ebx, &ecx, &edx);

 return edx;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool cpuid_function_is_indexed(u32 function)
{
 switch (function) {
 case 4:
 case 7:
 case 0xb:
 case 0xd:
 case 0xf:
 case 0x10:
 case 0x12:
 case 0x14:
 case 0x17:
 case 0x18:
 case 0x1d:
 case 0x1e:
 case 0x1f:
 case 0x8000001d:
  return true;
 }

 return false;
}




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) uint32_t hypervisor_cpuid_base(const char *sig, uint32_t leaves)
{
 uint32_t base, eax, signature[3];

 for (base = 0x40000000; base < 0x40010000; base += 0x100) {
  cpuid(base, &eax, &signature[0], &signature[1], &signature[2]);

  if (!memcmp(sig, signature, 12) &&
      (leaves == 0 || ((eax - base) >= leaves)))
   return base;
 }

 return 0;
}
# 20 "./arch/x86/include/asm/processor.h" 2



# 1 "./arch/x86/include/asm/msr.h" 1




# 1 "./arch/x86/include/asm/msr-index.h" 1
# 6 "./arch/x86/include/asm/msr.h" 2




# 1 "./arch/x86/include/generated/uapi/asm/errno.h" 1
# 11 "./arch/x86/include/asm/msr.h" 2
# 1 "./arch/x86/include/asm/cpumask.h" 1






extern void setup_cpu_local_masks(void);






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool arch_cpu_online(int cpu)
{
 return arch_test_bit(cpu, ((((const struct cpumask *)&__cpu_online_mask))->bits));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void arch_cpumask_clear_cpu(int cpu, struct cpumask *dstp)
{
 arch_clear_bit(cpumask_check(cpu), ((dstp)->bits));
}
# 12 "./arch/x86/include/asm/msr.h" 2
# 1 "./arch/x86/include/uapi/asm/msr.h" 1







# 1 "./include/uapi/linux/ioctl.h" 1




# 1 "./arch/x86/include/generated/uapi/asm/ioctl.h" 1
# 1 "./include/asm-generic/ioctl.h" 1




# 1 "./include/uapi/asm-generic/ioctl.h" 1
# 6 "./include/asm-generic/ioctl.h" 2





extern unsigned int __invalid_size_argument_for_IOC;
# 2 "./arch/x86/include/generated/uapi/asm/ioctl.h" 2
# 6 "./include/uapi/linux/ioctl.h" 2
# 9 "./arch/x86/include/uapi/asm/msr.h" 2
# 13 "./arch/x86/include/asm/msr.h" 2
# 1 "./arch/x86/include/asm/shared/msr.h" 1




struct msr {
 union {
  struct {
   u32 l;
   u32 h;
  };
  u64 q;
 };
};
# 14 "./arch/x86/include/asm/msr.h" 2

struct msr_info {
 u32 msr_no;
 struct msr reg;
 struct msr *msrs;
 int err;
};

struct msr_regs_info {
 u32 *regs;
 int err;
};

struct saved_msr {
 bool valid;
 struct msr_info info;
};

struct saved_msrs {
 unsigned int num;
 struct saved_msr *array;
};
# 58 "./arch/x86/include/asm/msr.h"
# 1 "./include/linux/tracepoint-defs.h" 1
# 12 "./include/linux/tracepoint-defs.h"
# 1 "./include/linux/static_key.h" 1
# 13 "./include/linux/tracepoint-defs.h" 2

struct static_call_key;

struct trace_print_flags {
 unsigned long mask;
 const char *name;
};

struct trace_print_flags_u64 {
 unsigned long long mask;
 const char *name;
};

struct tracepoint_func {
 void *func;
 void *data;
 int prio;
};

struct tracepoint {
 const char *name;
 struct static_key key;
 struct static_call_key *static_call_key;
 void *static_call_tramp;
 void *iterator;
 void *probestub;
 int (*regfunc)(void);
 void (*unregfunc)(void);
 struct tracepoint_func *funcs;
};


typedef const int tracepoint_ptr_t;




struct bpf_raw_event_map {
 struct tracepoint *tp;
 void *bpf_func;
 u32 num_args;
 u32 writable_size;
} __attribute__((__aligned__(32)));
# 59 "./arch/x86/include/asm/msr.h" 2


extern struct tracepoint __tracepoint_read_msr;
extern struct tracepoint __tracepoint_write_msr;
extern struct tracepoint __tracepoint_rdpmc;
extern void do_trace_write_msr(unsigned int msr, u64 val, int failed);
extern void do_trace_read_msr(unsigned int msr, u64 val, int failed);
extern void do_trace_rdpmc(unsigned int msr, u64 val, int failed);
# 80 "./arch/x86/include/asm/msr.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long long __rdmsr(unsigned int msr)
{
 unsigned long low, high;

 asm volatile("1: rdmsr\n"
       "2:\n"
       " .pushsection \"__ex_table\",\"a\"\n" " .balign 4\n" " .long (" "1b" ") - .\n" " .long (" "2b" ") - .\n" " .long " "9" " \n" " .popsection\n"
       : "=a" (low), "=d" (high) : "c" (msr));

 return ((low) | (high) << 32);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void __wrmsr(unsigned int msr, u32 low, u32 high)
{
 asm volatile("1: wrmsr\n"
       "2:\n"
       " .pushsection \"__ex_table\",\"a\"\n" " .balign 4\n" " .long (" "1b" ") - .\n" " .long (" "2b" ") - .\n" " .long " "8" " \n" " .popsection\n"
       : : "c" (msr), "a"(low), "d" (high) : "memory");
}
# 114 "./arch/x86/include/asm/msr.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long long native_read_msr(unsigned int msr)
{
 unsigned long long val;

 val = __rdmsr(msr);

 if (static_key_false(&(__tracepoint_read_msr).key))
  do_trace_read_msr(msr, val, 0);

 return val;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long long native_read_msr_safe(unsigned int msr,
            int *err)
{
 unsigned long low, high;

 asm volatile("1: rdmsr ; xor %[err],%[err]\n"
       "2:\n\t"
       " .pushsection \"__ex_table\",\"a\"\n" " .balign 4\n" " .long (" "1b" ") - .\n" " .long (" "2b" ") - .\n" ".macro extable_type_reg type:req reg:req\n" ".set .Lfound, 0\n" ".set .Lregnr, 0\n" ".irp rs,rax,rcx,rdx,rbx,rsp,rbp,rsi,rdi,r8,r9,r10,r11,r12,r13,r14,r15\n" ".ifc \\reg, %%\\rs\n" ".set .Lfound, .Lfound+1\n" ".long \\type + (.Lregnr << 8)\n" ".endif\n" ".set .Lregnr, .Lregnr+1\n" ".endr\n" ".set .Lregnr, 0\n" ".irp rs,eax,ecx,edx,ebx,esp,ebp,esi,edi,r8d,r9d,r10d,r11d,r12d,r13d,r14d,r15d\n" ".ifc \\reg, %%\\rs\n" ".set .Lfound, .Lfound+1\n" ".long \\type + (.Lregnr << 8)\n" ".endif\n" ".set .Lregnr, .Lregnr+1\n" ".endr\n" ".if (.Lfound != 1)\n" ".error \"extable_type_reg: bad register argument\"\n" ".endif\n" ".endm\n" "extable_type_reg reg=" "%[err]" ", type=" "11" " \n" ".purgem extable_type_reg\n" " .popsection\n"
       : [err] "=r" (*err), "=a" (low), "=d" (high)
       : "c" (msr));
 if (static_key_false(&(__tracepoint_read_msr).key))
  do_trace_read_msr(msr, ((low) | (high) << 32), *err);
 return ((low) | (high) << 32);
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __attribute__((no_instrument_function))
native_write_msr(unsigned int msr, u32 low, u32 high)
{
 __wrmsr(msr, low, high);

 if (static_key_false(&(__tracepoint_write_msr).key))
  do_trace_write_msr(msr, ((u64)high << 32 | low), 0);
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int __attribute__((no_instrument_function))
native_write_msr_safe(unsigned int msr, u32 low, u32 high)
{
 int err;

 asm volatile("1: wrmsr ; xor %[err],%[err]\n"
       "2:\n\t"
       " .pushsection \"__ex_table\",\"a\"\n" " .balign 4\n" " .long (" "1b" ") - .\n" " .long (" "2b" ") - .\n" ".macro extable_type_reg type:req reg:req\n" ".set .Lfound, 0\n" ".set .Lregnr, 0\n" ".irp rs,rax,rcx,rdx,rbx,rsp,rbp,rsi,rdi,r8,r9,r10,r11,r12,r13,r14,r15\n" ".ifc \\reg, %%\\rs\n" ".set .Lfound, .Lfound+1\n" ".long \\type + (.Lregnr << 8)\n" ".endif\n" ".set .Lregnr, .Lregnr+1\n" ".endr\n" ".set .Lregnr, 0\n" ".irp rs,eax,ecx,edx,ebx,esp,ebp,esi,edi,r8d,r9d,r10d,r11d,r12d,r13d,r14d,r15d\n" ".ifc \\reg, %%\\rs\n" ".set .Lfound, .Lfound+1\n" ".long \\type + (.Lregnr << 8)\n" ".endif\n" ".set .Lregnr, .Lregnr+1\n" ".endr\n" ".if (.Lfound != 1)\n" ".error \"extable_type_reg: bad register argument\"\n" ".endif\n" ".endm\n" "extable_type_reg reg=" "%[err]" ", type=" "10" " \n" ".purgem extable_type_reg\n" " .popsection\n"
       : [err] "=a" (err)
       : "c" (msr), "0" (low), "d" (high)
       : "memory");
 if (static_key_false(&(__tracepoint_write_msr).key))
  do_trace_write_msr(msr, ((u64)high << 32 | low), err);
 return err;
}

extern int rdmsr_safe_regs(u32 regs[8]);
extern int wrmsr_safe_regs(u32 regs[8]);
# 180 "./arch/x86/include/asm/msr.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long long rdtsc(void)
{
 unsigned long low, high;

 asm volatile("rdtsc" : "=a" (low), "=d" (high));

 return ((low) | (high) << 32);
}
# 197 "./arch/x86/include/asm/msr.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long long rdtsc_ordered(void)
{
 unsigned long low, high;
# 215 "./arch/x86/include/asm/msr.h"
 asm volatile("# ALT: oldinstr2\n" "661:\n\t" "rdtsc" "\n662:\n" "# ALT: padding2\n" ".skip -((" "((" "665""1""f-""664""1""f" ") ^ (((" "665""1""f-""664""1""f" ") ^ (" "665""2""f-""664""2""f" ")) & -(-((" "665""1""f-""664""1""f" ") < (" "665""2""f-""664""2""f" ")))))" " - (" "662b-661b" ")) > 0) * " "(" "((" "665""1""f-""664""1""f" ") ^ (((" "665""1""f-""664""1""f" ") ^ (" "665""2""f-""664""2""f" ")) & -(-((" "665""1""f-""664""1""f" ") < (" "665""2""f-""664""2""f" ")))))" " - (" "662b-661b" ")), 0x90\n" "663" ":\n" ".pushsection .altinstructions,\"a\"\n" " .long 661b - .\n" " .long " "664""1""f - .\n" " .4byte " "(20*32+ 2)" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""1""f-""664""1""f" "\n" " .long 661b - .\n" " .long " "664""2""f - .\n" " .4byte " "( 1*32+27)" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""2""f-""664""2""f" "\n" ".popsection\n" ".pushsection .altinstr_replacement, \"ax\"\n" "# ALT: replacement " "1" "\n" "664""1"":\n\t" "lfence; rdtsc" "\n" "665""1" ":\n" "# ALT: replacement " "2" "\n" "664""2"":\n\t" "rdtscp" "\n" "665""2" ":\n" ".popsection\n"


   : "=a" (low), "=d" (high)

   :: "ecx");

 return ((low) | (high) << 32);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long long native_read_pmc(int counter)
{
 unsigned long low, high;

 asm volatile("rdpmc" : "=a" (low), "=d" (high) : "c" (counter));
 if (static_key_false(&(__tracepoint_rdpmc).key))
  do_trace_rdpmc(counter, ((low) | (high) << 32), 0);
 return ((low) | (high) << 32);
}
# 252 "./arch/x86/include/asm/msr.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void wrmsr(unsigned int msr, u32 low, u32 high)
{
 native_write_msr(msr, low, high);
}




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void wrmsrl(unsigned int msr, u64 val)
{
 native_write_msr(msr, (u32)(val & 0xffffffffULL), (u32)(val >> 32));
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int wrmsr_safe(unsigned int msr, u32 low, u32 high)
{
 return native_write_msr_safe(msr, low, high);
}
# 281 "./arch/x86/include/asm/msr.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int rdmsrl_safe(unsigned int msr, unsigned long long *p)
{
 int err;

 *p = native_read_msr_safe(msr, &err);
 return err;
}
# 303 "./arch/x86/include/asm/msr.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int wrmsrl_safe(u32 msr, u64 val)
{
 return wrmsr_safe(msr, (u32)val, (u32)(val >> 32));
}

struct msr *msrs_alloc(void);
void msrs_free(struct msr *msrs);
int msr_set_bit(u32 msr, u8 bit);
int msr_clear_bit(u32 msr, u8 bit);


int rdmsr_on_cpu(unsigned int cpu, u32 msr_no, u32 *l, u32 *h);
int wrmsr_on_cpu(unsigned int cpu, u32 msr_no, u32 l, u32 h);
int rdmsrl_on_cpu(unsigned int cpu, u32 msr_no, u64 *q);
int wrmsrl_on_cpu(unsigned int cpu, u32 msr_no, u64 q);
void rdmsr_on_cpus(const struct cpumask *mask, u32 msr_no, struct msr *msrs);
void wrmsr_on_cpus(const struct cpumask *mask, u32 msr_no, struct msr *msrs);
int rdmsr_safe_on_cpu(unsigned int cpu, u32 msr_no, u32 *l, u32 *h);
int wrmsr_safe_on_cpu(unsigned int cpu, u32 msr_no, u32 l, u32 h);
int rdmsrl_safe_on_cpu(unsigned int cpu, u32 msr_no, u64 *q);
int wrmsrl_safe_on_cpu(unsigned int cpu, u32 msr_no, u64 q);
int rdmsr_safe_regs_on_cpu(unsigned int cpu, u32 regs[8]);
int wrmsr_safe_regs_on_cpu(unsigned int cpu, u32 regs[8]);
# 24 "./arch/x86/include/asm/processor.h" 2


# 1 "./arch/x86/include/asm/special_insns.h" 1
# 24 "./arch/x86/include/asm/special_insns.h"
void native_write_cr0(unsigned long val);

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long native_read_cr0(void)
{
 unsigned long val;
 asm volatile("mov %%cr0,%0\n\t" : "=r" (val) : "m"(*(unsigned int *)0x1000UL));
 return val;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long native_read_cr2(void)
{
 unsigned long val;
 asm volatile("mov %%cr2,%0\n\t" : "=r" (val) : "m"(*(unsigned int *)0x1000UL));
 return val;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void native_write_cr2(unsigned long val)
{
 asm volatile("mov %0,%%cr2": : "r" (val) : "memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long __native_read_cr3(void)
{
 unsigned long val;
 asm volatile("mov %%cr3,%0\n\t" : "=r" (val) : "m"(*(unsigned int *)0x1000UL));
 return val;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void native_write_cr3(unsigned long val)
{
 asm volatile("mov %0,%%cr3": : "r" (val) : "memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long native_read_cr4(void)
{
 unsigned long val;
# 72 "./arch/x86/include/asm/special_insns.h"
 asm volatile("mov %%cr4,%0\n\t" : "=r" (val) : "m"(*(unsigned int *)0x1000UL));

 return val;
}

void native_write_cr4(unsigned long val);


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) u32 rdpkru(void)
{
 u32 ecx = 0;
 u32 edx, pkru;





 asm volatile(".byte 0x0f,0x01,0xee\n\t"
       : "=a" (pkru), "=d" (edx)
       : "c" (ecx));
 return pkru;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void wrpkru(u32 pkru)
{
 u32 ecx = 0, edx = 0;





 asm volatile(".byte 0x0f,0x01,0xef\n\t"
       : : "a" (pkru), "c"(ecx), "d"(edx));
}
# 118 "./arch/x86/include/asm/special_insns.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void native_wbinvd(void)
{
 asm volatile("wbinvd": : :"memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long __read_cr4(void)
{
 return native_read_cr4();
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long read_cr0(void)
{
 return native_read_cr0();
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void write_cr0(unsigned long x)
{
 native_write_cr0(x);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long read_cr2(void)
{
 return native_read_cr2();
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void write_cr2(unsigned long x)
{
 native_write_cr2(x);
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long __read_cr3(void)
{
 return __native_read_cr3();
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void write_cr3(unsigned long x)
{
 native_write_cr3(x);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __write_cr4(unsigned long x)
{
 native_write_cr4(x);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void wbinvd(void)
{
 native_wbinvd();
}



static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void clflush(volatile void *__p)
{
 asm volatile("clflush %0" : "+m" (*(volatile char *)__p));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void clflushopt(volatile void *__p)
{
 asm __inline volatile ("# ALT: oldnstr\n" "661:\n\t" ".byte 0x3e; clflush %P0" "\n662:\n" "# ALT: padding\n" ".skip -(((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")) > 0) * " "((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")),0x90\n" "663" ":\n" ".pushsection .altinstructions,\"a\"\n" " .long 661b - .\n" " .long " "664""1""f - .\n" " .4byte " "( 9*32+23)" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""1""f-""664""1""f" "\n" ".popsection\n" ".pushsection .altinstr_replacement, \"ax\"\n" "# ALT: replacement " "1" "\n" "664""1"":\n\t" ".byte 0x66; clflush %P0" "\n" "665""1" ":\n" ".popsection\n" : "+m" (*(volatile char *)__p) : "i" (0))


                                              ;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void clwb(volatile void *__p)
{
 volatile struct { char x[64]; } *p = __p;

 asm volatile("# ALT: oldinstr2\n" "661:\n\t" ".byte 0x3e; clflush (%[pax])" "\n662:\n" "# ALT: padding2\n" ".skip -((" "((" "665""1""f-""664""1""f" ") ^ (((" "665""1""f-""664""1""f" ") ^ (" "665""2""f-""664""2""f" ")) & -(-((" "665""1""f-""664""1""f" ") < (" "665""2""f-""664""2""f" ")))))" " - (" "662b-661b" ")) > 0) * " "(" "((" "665""1""f-""664""1""f" ") ^ (((" "665""1""f-""664""1""f" ") ^ (" "665""2""f-""664""2""f" ")) & -(-((" "665""1""f-""664""1""f" ") < (" "665""2""f-""664""2""f" ")))))" " - (" "662b-661b" ")), 0x90\n" "663" ":\n" ".pushsection .altinstructions,\"a\"\n" " .long 661b - .\n" " .long " "664""1""f - .\n" " .4byte " "( 9*32+23)" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""1""f-""664""1""f" "\n" " .long 661b - .\n" " .long " "664""2""f - .\n" " .4byte " "( 9*32+24)" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""2""f-""664""2""f" "\n" ".popsection\n" ".pushsection .altinstr_replacement, \"ax\"\n" "# ALT: replacement " "1" "\n" "664""1"":\n\t" ".byte 0x66; clflush (%[pax])" "\n" "665""1" ":\n" "# ALT: replacement " "2" "\n" "664""2"":\n\t" ".byte 0x66, 0x0f, 0xae, 0x30" "\n" "665""2" ":\n" ".popsection\n"





  : [p] "+m" (*p)
  : [pax] "a" (p));
}
# 220 "./arch/x86/include/asm/special_insns.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void serialize(void)
{

 asm volatile(".byte 0xf, 0x1, 0xe8" ::: "memory");
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void movdir64b(void *dst, const void *src)
{
 const struct { char _[64]; } *__src = src;
 struct { char _[64]; } *__dst = dst;
# 243 "./arch/x86/include/asm/special_insns.h"
 asm volatile(".byte 0x66, 0x0f, 0x38, 0xf8, 0x02"
       : "+m" (*__dst)
       : "m" (*__src), "a" (__dst), "d" (__src));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void movdir64b_io(void *dst, const void *src)
{
 movdir64b((void *)dst, src);
}
# 272 "./arch/x86/include/asm/special_insns.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int enqcmds(void *dst, const void *src)
{
 const struct { char _[64]; } *__src = src;
 struct { char _[64]; } *__dst = dst;
 bool zf;






 asm volatile(".byte 0xf3, 0x0f, 0x38, 0xf8, 0x02, 0x66, 0x90"
       "\n\t/* output condition code " "z" "*/\n"
       : "=@cc" "z" (zf), "+m" (*__dst)
       : "m" (*__src), "a" (__dst), "d" (__src));


 if (zf)
  return -11;

 return 0;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void tile_release(void)
{




 asm volatile(".byte 0xc4, 0xe2, 0x78, 0x49, 0xc0");
}
# 27 "./arch/x86/include/asm/processor.h" 2
# 1 "./arch/x86/include/asm/fpu/types.h" 1
# 14 "./arch/x86/include/asm/fpu/types.h"
struct fregs_state {
 u32 cwd;
 u32 swd;
 u32 twd;
 u32 fip;
 u32 fcs;
 u32 foo;
 u32 fos;


 u32 st_space[20];


 u32 status;
};







struct fxregs_state {
 u16 cwd;
 u16 swd;
 u16 twd;
 u16 fop;
 union {
  struct {
   u64 rip;
   u64 rdp;
  };
  struct {
   u32 fip;
   u32 fcs;
   u32 foo;
   u32 fos;
  };
 };
 u32 mxcsr;
 u32 mxcsr_mask;


 u32 st_space[32];


 u32 xmm_space[64];

 u32 padding[12];

 union {
  u32 padding1[12];
  u32 sw_reserved[12];
 };

} __attribute__((aligned(16)));
# 81 "./arch/x86/include/asm/fpu/types.h"
struct swregs_state {
 u32 cwd;
 u32 swd;
 u32 twd;
 u32 fip;
 u32 fcs;
 u32 foo;
 u32 fos;

 u32 st_space[20];
 u8 ftop;
 u8 changed;
 u8 lookahead;
 u8 no_update;
 u8 rm;
 u8 alimit;
 struct math_emu_info *info;
 u32 entry_eip;
};




enum xfeature {
 XFEATURE_FP,
 XFEATURE_SSE,




 XFEATURE_YMM,
 XFEATURE_BNDREGS,
 XFEATURE_BNDCSR,
 XFEATURE_OPMASK,
 XFEATURE_ZMM_Hi256,
 XFEATURE_Hi16_ZMM,
 XFEATURE_PT_UNIMPLEMENTED_SO_FAR,
 XFEATURE_PKRU,
 XFEATURE_PASID,
 XFEATURE_CET_USER,
 XFEATURE_CET_KERNEL_UNUSED,
 XFEATURE_RSRVD_COMP_13,
 XFEATURE_RSRVD_COMP_14,
 XFEATURE_LBR,
 XFEATURE_RSRVD_COMP_16,
 XFEATURE_XTILE_CFG,
 XFEATURE_XTILE_DATA,

 XFEATURE_MAX,
};
# 163 "./arch/x86/include/asm/fpu/types.h"
struct reg_128_bit {
 u8 regbytes[128/8];
};
struct reg_256_bit {
 u8 regbytes[256/8];
};
struct reg_512_bit {
 u8 regbytes[512/8];
};
struct reg_1024_byte {
 u8 regbytes[1024];
};
# 186 "./arch/x86/include/asm/fpu/types.h"
struct ymmh_struct {
 struct reg_128_bit hi_ymm[16];
} __attribute__((__packed__));



struct mpx_bndreg {
 u64 lower_bound;
 u64 upper_bound;
} __attribute__((__packed__));



struct mpx_bndreg_state {
 struct mpx_bndreg bndreg[4];
} __attribute__((__packed__));






struct mpx_bndcsr {
 u64 bndcfgu;
 u64 bndstatus;
} __attribute__((__packed__));




struct mpx_bndcsr_state {
 union {
  struct mpx_bndcsr bndcsr;
  u8 pad_to_64_bytes[64];
 };
} __attribute__((__packed__));







struct avx_512_opmask_state {
 u64 opmask_reg[8];
} __attribute__((__packed__));






struct avx_512_zmm_uppers_state {
 struct reg_256_bit zmm_upper[16];
} __attribute__((__packed__));





struct avx_512_hi16_state {
 struct reg_512_bit hi16_zmm[16];
} __attribute__((__packed__));





struct pkru_state {
 u32 pkru;
 u32 pad;
} __attribute__((__packed__));




struct cet_user_state {

 u64 user_cet;

 u64 user_ssp;
};






struct lbr_entry {
 u64 from;
 u64 to;
 u64 info;
};

struct arch_lbr_state {
 u64 lbr_ctl;
 u64 lbr_depth;
 u64 ler_from;
 u64 ler_to;
 u64 ler_info;
 struct lbr_entry entries[];
};




struct xtile_cfg {
 u64 tcfg[8];
} __attribute__((__packed__));







struct xtile_data {
 struct reg_1024_byte tmm;
} __attribute__((__packed__));





struct ia32_pasid_state {
 u64 pasid;
} __attribute__((__packed__));

struct xstate_header {
 u64 xfeatures;
 u64 xcomp_bv;
 u64 reserved[6];
} __attribute__((packed));
# 335 "./arch/x86/include/asm/fpu/types.h"
struct xregs_state {
 struct fxregs_state i387;
 struct xstate_header header;
 u8 extended_state_area[];
} __attribute__ ((packed, aligned (64)));
# 350 "./arch/x86/include/asm/fpu/types.h"
union fpregs_state {
 struct fregs_state fsave;
 struct fxregs_state fxsave;
 struct swregs_state soft;
 struct xregs_state xsave;
 u8 __padding[((1UL) << 12)];
};

struct fpstate {

 unsigned int size;


 unsigned int user_size;


 u64 xfeatures;


 u64 user_xfeatures;


 u64 xfd;


 unsigned int is_valloc : 1;


 unsigned int is_guest : 1;
# 393 "./arch/x86/include/asm/fpu/types.h"
 unsigned int is_confidential : 1;


 unsigned int in_use : 1;


 union fpregs_state regs;


} __attribute__((__aligned__(64)));



struct fpu_state_perm {
# 426 "./arch/x86/include/asm/fpu/types.h"
 u64 __state_perm;







 unsigned int __state_size;







 unsigned int __user_state_size;
};






struct fpu {
# 463 "./arch/x86/include/asm/fpu/types.h"
 unsigned int last_cpu;






 unsigned long avx512_timestamp;







 struct fpstate *fpstate;







 struct fpstate *__task_fpstate;






 struct fpu_state_perm perm;






 struct fpu_state_perm guest_perm;
# 510 "./arch/x86/include/asm/fpu/types.h"
 struct fpstate __fpstate;




};




struct fpu_guest {




 u64 xfeatures;






 u64 perm;




 u64 xfd_err;




 unsigned int uabi_size;




 struct fpstate *fpstate;
};




struct fpu_state_config {






 unsigned int max_size;
# 569 "./arch/x86/include/asm/fpu/types.h"
 unsigned int default_size;







 u64 max_features;
# 586 "./arch/x86/include/asm/fpu/types.h"
 u64 default_features;






 u64 legacy_features;
};


extern struct fpu_state_config fpu_kernel_cfg, fpu_user_cfg;
# 28 "./arch/x86/include/asm/processor.h" 2

# 1 "./arch/x86/include/asm/vmxfeatures.h" 1
# 30 "./arch/x86/include/asm/processor.h" 2
# 1 "./arch/x86/include/asm/vdso/processor.h" 1
# 11 "./arch/x86/include/asm/vdso/processor.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void rep_nop(void)
{
 asm volatile("rep; nop" ::: "memory");
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void cpu_relax(void)
{
 rep_nop();
}

struct getcpu_cache;

__attribute__((no_instrument_function)) long __vdso_getcpu(unsigned *cpu, unsigned *node, struct getcpu_cache *unused);
# 31 "./arch/x86/include/asm/processor.h" 2
# 1 "./arch/x86/include/asm/shstk.h" 1







struct task_struct;
struct ksignal;
# 25 "./arch/x86/include/asm/shstk.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) long shstk_prctl(struct task_struct *task, int option,
          unsigned long arg2) { return -22; }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void reset_thread_features(void) {}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long shstk_alloc_thread_stack(struct task_struct *p,
           unsigned long clone_flags,
           unsigned long stack_size) { return 0; }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void shstk_free(struct task_struct *p) {}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int setup_signal_shadow_stack(struct ksignal *ksig) { return 0; }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int restore_signal_shadow_stack(void) { return 0; }
# 32 "./arch/x86/include/asm/processor.h" 2

# 1 "./include/linux/personality.h" 1




# 1 "./include/uapi/linux/personality.h" 1
# 11 "./include/uapi/linux/personality.h"
enum {
 UNAME26 = 0x0020000,
 ADDR_NO_RANDOMIZE = 0x0040000,
 FDPIC_FUNCPTRS = 0x0080000,


 MMAP_PAGE_ZERO = 0x0100000,
 ADDR_COMPAT_LAYOUT = 0x0200000,
 READ_IMPLIES_EXEC = 0x0400000,
 ADDR_LIMIT_32BIT = 0x0800000,
 SHORT_INODE = 0x1000000,
 WHOLE_SECONDS = 0x2000000,
 STICKY_TIMEOUTS = 0x4000000,
 ADDR_LIMIT_3GB = 0x8000000,
};
# 42 "./include/uapi/linux/personality.h"
enum {
 PER_LINUX = 0x0000,
 PER_LINUX_32BIT = 0x0000 | ADDR_LIMIT_32BIT,
 PER_LINUX_FDPIC = 0x0000 | FDPIC_FUNCPTRS,
 PER_SVR4 = 0x0001 | STICKY_TIMEOUTS | MMAP_PAGE_ZERO,
 PER_SVR3 = 0x0002 | STICKY_TIMEOUTS | SHORT_INODE,
 PER_SCOSVR3 = 0x0003 | STICKY_TIMEOUTS |
      WHOLE_SECONDS | SHORT_INODE,
 PER_OSR5 = 0x0003 | STICKY_TIMEOUTS | WHOLE_SECONDS,
 PER_WYSEV386 = 0x0004 | STICKY_TIMEOUTS | SHORT_INODE,
 PER_ISCR4 = 0x0005 | STICKY_TIMEOUTS,
 PER_BSD = 0x0006,
 PER_SUNOS = 0x0006 | STICKY_TIMEOUTS,
 PER_XENIX = 0x0007 | STICKY_TIMEOUTS | SHORT_INODE,
 PER_LINUX32 = 0x0008,
 PER_LINUX32_3GB = 0x0008 | ADDR_LIMIT_3GB,
 PER_IRIX32 = 0x0009 | STICKY_TIMEOUTS,
 PER_IRIXN32 = 0x000a | STICKY_TIMEOUTS,
 PER_IRIX64 = 0x000b | STICKY_TIMEOUTS,
 PER_RISCOS = 0x000c,
 PER_SOLARIS = 0x000d | STICKY_TIMEOUTS,
 PER_UW7 = 0x000e | STICKY_TIMEOUTS | MMAP_PAGE_ZERO,
 PER_OSF4 = 0x000f,
 PER_HPUX = 0x0010,
 PER_MASK = 0x00ff,
};
# 6 "./include/linux/personality.h" 2
# 34 "./arch/x86/include/asm/processor.h" 2


# 1 "./include/linux/math64.h" 1






# 1 "./include/vdso/math64.h" 1




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) u32
__iter_div_u64_rem(u64 dividend, u32 divisor, u64 *remainder)
{
 u32 ret = 0;

 while (dividend >= divisor) {


  asm("" : "+rm"(dividend));

  dividend -= divisor;
  ret++;
 }

 *remainder = dividend;

 return ret;
}
# 8 "./include/linux/math64.h" 2
# 26 "./include/linux/math64.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) u64 div_u64_rem(u64 dividend, u32 divisor, u32 *remainder)
{
 *remainder = dividend % divisor;
 return dividend / divisor;
}
# 40 "./include/linux/math64.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) s64 div_s64_rem(s64 dividend, s32 divisor, s32 *remainder)
{
 *remainder = dividend % divisor;
 return dividend / divisor;
}
# 54 "./include/linux/math64.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) u64 div64_u64_rem(u64 dividend, u64 divisor, u64 *remainder)
{
 *remainder = dividend % divisor;
 return dividend / divisor;
}
# 67 "./include/linux/math64.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) u64 div64_u64(u64 dividend, u64 divisor)
{
 return dividend / divisor;
}
# 79 "./include/linux/math64.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) s64 div64_s64(s64 dividend, s64 divisor)
{
 return dividend / divisor;
}
# 127 "./include/linux/math64.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) u64 div_u64(u64 dividend, u32 divisor)
{
 u32 remainder;
 return div_u64_rem(dividend, divisor, &remainder);
}
# 142 "./include/linux/math64.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) s64 div_s64(s64 dividend, s32 divisor)
{
 s32 remainder;
 return div_s64_rem(dividend, divisor, &remainder);
}


u32 iter_div_u64_rem(u64 dividend, u32 divisor, u64 *remainder);





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) u64 mul_u32_u32(u32 a, u32 b)
{
 return (u64)a * b;
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) u64 mul_u64_u32_shr(u64 a, u32 mul, unsigned int shift)
{
 return (u64)(((unsigned __int128)a * mul) >> shift);
}



static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) u64 mul_u64_u64_shr(u64 a, u64 mul, unsigned int shift)
{
 return (u64)(((unsigned __int128)a * mul) >> shift);
}
# 243 "./include/linux/math64.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) u64 mul_s64_u64_shr(s64 a, u64 b, unsigned int shift)
{
 u64 ret;





 ret = mul_u64_u64_shr(__builtin_choose_expr( __builtin_types_compatible_p(typeof(a), signed long long) || __builtin_types_compatible_p(typeof(a), unsigned long long), ({ signed long long __x = (a); __x < 0 ? -__x : __x; }), __builtin_choose_expr( __builtin_types_compatible_p(typeof(a), signed long) || __builtin_types_compatible_p(typeof(a), unsigned long), ({ signed long __x = (a); __x < 0 ? -__x : __x; }), __builtin_choose_expr( __builtin_types_compatible_p(typeof(a), signed int) || __builtin_types_compatible_p(typeof(a), unsigned int), ({ signed int __x = (a); __x < 0 ? -__x : __x; }), __builtin_choose_expr( __builtin_types_compatible_p(typeof(a), signed short) || __builtin_types_compatible_p(typeof(a), unsigned short), ({ signed short __x = (a); __x < 0 ? -__x : __x; }), __builtin_choose_expr( __builtin_types_compatible_p(typeof(a), signed char) || __builtin_types_compatible_p(typeof(a), unsigned char), ({ signed char __x = (a); __x < 0 ? -__x : __x; }), __builtin_choose_expr( __builtin_types_compatible_p(typeof(a), char), (char)({ signed char __x = (a); __x<0?-__x:__x; }), ((void)0))))))), b, shift);

 if (a < 0)
  ret = -((s64) ret);

 return ret;
}
# 289 "./include/linux/math64.h"
u64 mul_u64_u64_div_u64(u64 a, u64 mul, u64 div);
# 37 "./arch/x86/include/asm/processor.h" 2
# 64 "./arch/x86/include/asm/processor.h"
enum tlb_infos {
 ENTRIES,
 NR_INFO
};

extern u16 __attribute__((__section__(".data..read_mostly"))) tlb_lli_4k[NR_INFO];
extern u16 __attribute__((__section__(".data..read_mostly"))) tlb_lli_2m[NR_INFO];
extern u16 __attribute__((__section__(".data..read_mostly"))) tlb_lli_4m[NR_INFO];
extern u16 __attribute__((__section__(".data..read_mostly"))) tlb_lld_4k[NR_INFO];
extern u16 __attribute__((__section__(".data..read_mostly"))) tlb_lld_2m[NR_INFO];
extern u16 __attribute__((__section__(".data..read_mostly"))) tlb_lld_4m[NR_INFO];
extern u16 __attribute__((__section__(".data..read_mostly"))) tlb_lld_1g[NR_INFO];





struct cpuinfo_topology {

 u32 apicid;

 u32 initial_apicid;


 u32 pkg_id;


 u32 die_id;


 u32 cu_id;


 u32 core_id;


 u32 logical_pkg_id;
 u32 logical_die_id;


 u32 llc_id;
 u32 l2c_id;
};

struct cpuinfo_x86 {
 __u8 x86;
 __u8 x86_vendor;
 __u8 x86_model;
 __u8 x86_stepping;


 int x86_tlbsize;


 __u32 vmx_capability[5];

 __u8 x86_virt_bits;
 __u8 x86_phys_bits;

 __u8 x86_coreid_bits;

 __u32 extended_cpuid_level;

 int cpuid_level;





 union {
  __u32 x86_capability[22 + 2];
  unsigned long x86_capability_alignment;
 };
 char x86_vendor_id[16];
 char x86_model_id[64];
 struct cpuinfo_topology topo;

 unsigned int x86_cache_size;
 int x86_cache_alignment;

 int x86_cache_max_rmid;
 int x86_cache_occ_scale;
 int x86_cache_mbm_width_offset;
 int x86_power;
 unsigned long loops_per_jiffy;

 u64 ppin;

 u16 x86_max_cores;
 u16 x86_clflush_size;

 u16 booted_cores;

 u16 cpu_index;

 bool smt_active;
 u32 microcode;

 u8 x86_cache_bits;
 unsigned initialized : 1;
} __attribute__((__designated_init__));
# 183 "./arch/x86/include/asm/processor.h"
extern struct cpuinfo_x86 boot_cpu_data;
extern struct cpuinfo_x86 new_cpu_data;

extern __u32 cpu_caps_cleared[22 + 2];
extern __u32 cpu_caps_set[22 + 2];


extern __attribute__((section(".data..percpu" "..read_mostly"))) __typeof__(struct cpuinfo_x86) cpu_info;






extern const struct seq_operations cpuinfo_op;



extern void cpu_detect(struct cpuinfo_x86 *c);

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long long l1tf_pfn_limit(void)
{
 return ((((1ULL))) << (boot_cpu_data.x86_cache_bits - 1 - 12));
}

extern void early_cpu_init(void);
extern void identify_secondary_cpu(struct cpuinfo_x86 *);
extern void print_cpu_info(struct cpuinfo_x86 *);
void print_cpu_msr(struct cpuinfo_x86 *);




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long read_cr3_pa(void)
{
 return __read_cr3() & ((((signed long)(~(((1UL) << 12)-1))) & ((phys_addr_t)((1ULL << 52) - 1))));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long native_read_cr3_pa(void)
{
 return __native_read_cr3() & ((((signed long)(~(((1UL) << 12)-1))) & ((phys_addr_t)((1ULL << 52) - 1))));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void load_cr3(pgd_t *pgdir)
{
 write_cr3((__phys_addr_nodebug((unsigned long)(pgdir)) | 0ULL));
}
# 285 "./arch/x86/include/asm/processor.h"
struct x86_hw_tss {
 u32 reserved1;
 u64 sp0;
 u64 sp1;






 u64 sp2;

 u64 reserved2;
 u64 ist[7];
 u32 reserved3;
 u32 reserved4;
 u16 reserved5;
 u16 io_bitmap_base;

} __attribute__((packed));
# 338 "./arch/x86/include/asm/processor.h"
struct entry_stack {
 char stack[((1UL) << 12)];
};

struct entry_stack_page {
 struct entry_stack stack;
} __attribute__((__aligned__(((1UL) << 12))));




struct x86_io_bitmap {

 u64 prev_sequence;
# 360 "./arch/x86/include/asm/processor.h"
 unsigned int prev_max;







 unsigned long bitmap[((65536 / 8) / sizeof(long)) + 1];





 unsigned long mapall[((65536 / 8) / sizeof(long)) + 1];
};

struct tss_struct {





 struct x86_hw_tss x86_tss;

 struct x86_io_bitmap io_bitmap;
} __attribute__((__aligned__(((1UL) << 12))));

extern __attribute__((section(".data..percpu" "..page_aligned"))) __typeof__(struct tss_struct) cpu_tss_rw __attribute__((__aligned__(((1UL) << 12))));


struct irq_stack {
 char stack[(((1UL) << 12) << (2 + 0))];
} __attribute__((__aligned__((((1UL) << 12) << (2 + 0)))));


struct fixed_percpu_data {
# 405 "./arch/x86/include/asm/processor.h"
 char gs_base[40];
 unsigned long stack_canary;
};

extern __attribute__((section(".data..percpu" "..first"))) __typeof__(struct fixed_percpu_data) fixed_percpu_data __attribute__((__externally_visible__));
extern typeof(fixed_percpu_data) init_per_cpu__fixed_percpu_data;

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long cpu_kernelmode_gs_base(int cpu)
{
 return (unsigned long)(*({ do { const void *__vpp_verify = (typeof((&(fixed_percpu_data.gs_base)) + 0))((void *)0); (void)__vpp_verify; } while (0); ({ unsigned long __ptr; __asm__ ("" : "=r"(__ptr) : "0"((typeof(*((&(fixed_percpu_data.gs_base)))) *)((&(fixed_percpu_data.gs_base))))); (typeof((typeof(*((&(fixed_percpu_data.gs_base)))) *)((&(fixed_percpu_data.gs_base))))) (__ptr + (((__per_cpu_offset[(cpu)])))); }); }));
}

extern void entry_SYSCALL32_ignore(void);


void current_save_fsgs(void);






struct perf_event;

struct thread_struct {

 struct desc_struct tls_array[3];



 unsigned long sp;



 unsigned short es;
 unsigned short ds;
 unsigned short fsindex;
 unsigned short gsindex;



 unsigned long fsbase;
 unsigned long gsbase;
# 458 "./arch/x86/include/asm/processor.h"
 struct perf_event *ptrace_bps[4];

 unsigned long virtual_dr6;

 unsigned long ptrace_dr7;

 unsigned long cr2;
 unsigned long trap_nr;
 unsigned long error_code;





 struct io_bitmap *io_bitmap;






 unsigned long iopl_emul;

 unsigned int iopl_warn:1;
# 490 "./arch/x86/include/asm/processor.h"
 u32 pkru;
# 500 "./arch/x86/include/asm/processor.h"
 struct fpu fpu;




};

extern void fpu_thread_struct_whitelist(unsigned long *offset, unsigned long *size);

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void arch_thread_struct_whitelist(unsigned long *offset,
      unsigned long *size)
{
 fpu_thread_struct_whitelist(offset, size);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void
native_load_sp0(unsigned long sp0)
{
 do { do { const void *__vpp_verify = (typeof((&(cpu_tss_rw.x86_tss.sp0)) + 0))((void *)0); (void)__vpp_verify; } while (0); switch(sizeof(cpu_tss_rw.x86_tss.sp0)) { case 1: do { u8 pto_val__ = ((u8)(((unsigned long) sp0) & 0xff)); if (0) { typeof((cpu_tss_rw.x86_tss.sp0)) pto_tmp__; pto_tmp__ = (sp0); (void)pto_tmp__; } asm volatile("mov" "b " "%[val]" ", " "%%""gs"":" "%" "[var]" : [var] "+m" ((cpu_tss_rw.x86_tss.sp0)) : [val] "qi" (pto_val__)); } while (0);break; case 2: do { u16 pto_val__ = ((u16)(((unsigned long) sp0) & 0xffff)); if (0) { typeof((cpu_tss_rw.x86_tss.sp0)) pto_tmp__; pto_tmp__ = (sp0); (void)pto_tmp__; } asm volatile("mov" "w " "%[val]" ", " "%%""gs"":" "%" "[var]" : [var] "+m" ((cpu_tss_rw.x86_tss.sp0)) : [val] "ri" (pto_val__)); } while (0);break; case 4: do { u32 pto_val__ = ((u32)(((unsigned long) sp0) & 0xffffffff)); if (0) { typeof((cpu_tss_rw.x86_tss.sp0)) pto_tmp__; pto_tmp__ = (sp0); (void)pto_tmp__; } asm volatile("mov" "l " "%[val]" ", " "%%""gs"":" "%" "[var]" : [var] "+m" ((cpu_tss_rw.x86_tss.sp0)) : [val] "ri" (pto_val__)); } while (0);break; case 8: do { u64 pto_val__ = ((u64)(sp0)); if (0) { typeof((cpu_tss_rw.x86_tss.sp0)) pto_tmp__; pto_tmp__ = (sp0); (void)pto_tmp__; } asm volatile("mov" "q " "%[val]" ", " "%%""gs"":" "%" "[var]" : [var] "+m" ((cpu_tss_rw.x86_tss.sp0)) : [val] "re" (pto_val__)); } while (0);break; default: __bad_size_call_parameter();break; } } while (0);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void native_swapgs(void)
{

 asm volatile("swapgs" ::: "memory");

}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long current_top_of_stack(void)
{





 return ({ typeof(pcpu_hot.top_of_stack) pscr_ret__; do { const void *__vpp_verify = (typeof((&(pcpu_hot.top_of_stack)) + 0))((void *)0); (void)__vpp_verify; } while (0); switch(sizeof(pcpu_hot.top_of_stack)) { case 1: pscr_ret__ = ({ u8 pfo_val__; asm("mov" "b " "%%""gs"":" "%" "P[var]" ", " "%[val]" : [val] "=" "q" (pfo_val__) : [var] "p" (&(pcpu_hot.top_of_stack))); (typeof(pcpu_hot.top_of_stack))(unsigned long) pfo_val__; }); break; case 2: pscr_ret__ = ({ u16 pfo_val__; asm("mov" "w " "%%""gs"":" "%" "P[var]" ", " "%[val]" : [val] "=" "r" (pfo_val__) : [var] "p" (&(pcpu_hot.top_of_stack))); (typeof(pcpu_hot.top_of_stack))(unsigned long) pfo_val__; }); break; case 4: pscr_ret__ = ({ u32 pfo_val__; asm("mov" "l " "%%""gs"":" "%" "P[var]" ", " "%[val]" : [val] "=" "r" (pfo_val__) : [var] "p" (&(pcpu_hot.top_of_stack))); (typeof(pcpu_hot.top_of_stack))(unsigned long) pfo_val__; }); break; case 8: pscr_ret__ = ({ u64 pfo_val__; asm("mov" "q " "%%""gs"":" "%" "P[var]" ", " "%[val]" : [val] "=" "r" (pfo_val__) : [var] "p" (&(pcpu_hot.top_of_stack))); (typeof(pcpu_hot.top_of_stack))(unsigned long) pfo_val__; }); break; default: __bad_size_call_parameter(); break; } pscr_ret__; });
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool on_thread_stack(void)
{
 return (unsigned long)(current_top_of_stack() -
          current_stack_pointer) < (((1UL) << 12) << (2 + 0));
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void load_sp0(unsigned long sp0)
{
 native_load_sp0(sp0);
}



unsigned long __get_wchan(struct task_struct *p);

extern void select_idle_routine(const struct cpuinfo_x86 *c);
extern void amd_e400_c1e_apic_setup(void);

extern unsigned long boot_option_idle_override;

enum idle_boot_override {IDLE_NO_OVERRIDE=0, IDLE_HALT, IDLE_NOMWAIT,
    IDLE_POLL};

extern void enable_sep_cpu(void);



extern struct desc_ptr early_gdt_descr;

extern void switch_gdt_and_percpu_base(int);
extern void load_direct_gdt(int);
extern void load_fixmap_gdt(int);
extern void cpu_init(void);
extern void cpu_init_exception_handling(void);
extern void cr4_init(void);

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) unsigned long get_debugctlmsr(void)
{
 unsigned long debugctlmsr = 0;





 ((debugctlmsr) = native_read_msr((0x000001d9)));

 return debugctlmsr;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void update_debugctlmsr(unsigned long debugctlmsr)
{




 wrmsrl(0x000001d9, debugctlmsr);
}

extern void set_task_blockstep(struct task_struct *task, bool on);


extern int bootloader_type;
extern int bootloader_version;

extern char ignore_fpu_irq;
# 624 "./arch/x86/include/asm/processor.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void prefetch(const void *x)
{
 asm __inline volatile ("# ALT: oldnstr\n" "661:\n\t" "prefetcht0 %P1" "\n662:\n" "# ALT: padding\n" ".skip -(((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")) > 0) * " "((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")),0x90\n" "663" ":\n" ".pushsection .altinstructions,\"a\"\n" " .long 661b - .\n" " .long " "664""1""f - .\n" " .4byte " "( 0*32+25)" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""1""f-""664""1""f" "\n" ".popsection\n" ".pushsection .altinstr_replacement, \"ax\"\n" "# ALT: replacement " "1" "\n" "664""1"":\n\t" "prefetchnta %P1" "\n" "665""1" ":\n" ".popsection\n" : : "i" (0), "m" (*(const char *)x))

                            ;
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void prefetchw(const void *x)
{
 asm __inline volatile ("# ALT: oldnstr\n" "661:\n\t" "prefetcht0 %P1" "\n662:\n" "# ALT: padding\n" ".skip -(((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")) > 0) * " "((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")),0x90\n" "663" ":\n" ".pushsection .altinstructions,\"a\"\n" " .long 661b - .\n" " .long " "664""1""f - .\n" " .4byte " "( 6*32+ 8)" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""1""f-""664""1""f" "\n" ".popsection\n" ".pushsection .altinstr_replacement, \"ax\"\n" "# ALT: replacement " "1" "\n" "664""1"":\n\t" "prefetchw %P1" "\n" "665""1" ":\n" ".popsection\n" : : "i" (0), "m" (*(const char *)x))

                            ;
}
# 664 "./arch/x86/include/asm/processor.h"
extern unsigned long __end_init_task[];





extern unsigned long KSTK_ESP(struct task_struct *task);



extern void start_thread(struct pt_regs *regs, unsigned long new_ip,
            unsigned long new_sp);
# 690 "./arch/x86/include/asm/processor.h"
extern int get_tsc_mode(unsigned long adr);
extern int set_tsc_mode(unsigned int val);

extern __attribute__((section(".data..percpu" ""))) __typeof__(u64) msr_misc_features_shadow;

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) u32 per_cpu_llc_id(unsigned int cpu)
{
 return (*({ do { const void *__vpp_verify = (typeof((&(cpu_info.topo.llc_id)) + 0))((void *)0); (void)__vpp_verify; } while (0); ({ unsigned long __ptr; __asm__ ("" : "=r"(__ptr) : "0"((typeof(*((&(cpu_info.topo.llc_id)))) *)((&(cpu_info.topo.llc_id))))); (typeof((typeof(*((&(cpu_info.topo.llc_id)))) *)((&(cpu_info.topo.llc_id))))) (__ptr + (((__per_cpu_offset[(cpu)])))); }); }));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) u32 per_cpu_l2c_id(unsigned int cpu)
{
 return (*({ do { const void *__vpp_verify = (typeof((&(cpu_info.topo.l2c_id)) + 0))((void *)0); (void)__vpp_verify; } while (0); ({ unsigned long __ptr; __asm__ ("" : "=r"(__ptr) : "0"((typeof(*((&(cpu_info.topo.l2c_id)))) *)((&(cpu_info.topo.l2c_id))))); (typeof((typeof(*((&(cpu_info.topo.l2c_id)))) *)((&(cpu_info.topo.l2c_id))))) (__ptr + (((__per_cpu_offset[(cpu)])))); }); }));
}


extern u32 amd_get_nodes_per_socket(void);
extern u32 amd_get_highest_perf(void);
extern void amd_clear_divider(void);
extern void amd_check_microcode(void);







extern unsigned long arch_align_stack(unsigned long sp);
void free_init_pages(const char *what, unsigned long begin, unsigned long end);
extern void free_kernel_image_pages(const char *what, void *begin, void *end);

void default_idle(void);






void __attribute__((__noreturn__)) stop_this_cpu(void *dummy);
void microcode_check(struct cpuinfo_x86 *prev_info);
void store_cpu_caps(struct cpuinfo_x86 *info);

enum l1tf_mitigations {
 L1TF_MITIGATION_OFF,
 L1TF_MITIGATION_FLUSH_NOWARN,
 L1TF_MITIGATION_FLUSH,
 L1TF_MITIGATION_FLUSH_NOSMT,
 L1TF_MITIGATION_FULL,
 L1TF_MITIGATION_FULL_FORCE
};

extern enum l1tf_mitigations l1tf_mitigation;

enum mds_mitigations {
 MDS_MITIGATION_OFF,
 MDS_MITIGATION_FULL,
 MDS_MITIGATION_VMWERV,
};

extern bool gds_ucode_mitigated(void);
# 764 "./arch/x86/include/asm/processor.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void weak_wrmsr_fence(void)
{
 asm __inline volatile ("# ALT: oldnstr\n" "661:\n\t" "mfence; lfence" "\n662:\n" "# ALT: padding\n" ".skip -(((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")) > 0) * " "((" "665""1""f-""664""1""f" ")-(" "662b-661b" ")),0x90\n" "663" ":\n" ".pushsection .altinstructions,\"a\"\n" " .long 661b - .\n" " .long " "664""1""f - .\n" " .4byte " "(((1 << 0) << 16) | ((11*32+27)))" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""1""f-""664""1""f" "\n" ".popsection\n" ".pushsection .altinstr_replacement, \"ax\"\n" "# ALT: replacement " "1" "\n" "664""1"":\n\t" "" "\n" "665""1" ":\n" ".popsection\n" : : : "memory");
}
# 6 "./arch/x86/include/asm/cpufeature.h" 2







enum cpuid_leafs
{
 CPUID_1_EDX = 0,
 CPUID_8000_0001_EDX,
 CPUID_8086_0001_EDX,
 CPUID_LNX_1,
 CPUID_1_ECX,
 CPUID_C000_0001_EDX,
 CPUID_8000_0001_ECX,
 CPUID_LNX_2,
 CPUID_LNX_3,
 CPUID_7_0_EBX,
 CPUID_D_1_EAX,
 CPUID_LNX_4,
 CPUID_7_1_EAX,
 CPUID_8000_0008_EBX,
 CPUID_6_EAX,
 CPUID_8000_000A_EDX,
 CPUID_7_ECX,
 CPUID_8000_0007_EBX,
 CPUID_7_EDX,
 CPUID_8000_001F_EAX,
 CPUID_8000_0021_EAX,
 CPUID_LNX_5,
 NR_CPUID_WORDS,
};




extern const char * const x86_cap_flags[22*32];
extern const char * const x86_power_flags[32];







extern const char * const x86_bug_flags[2*32];
# 150 "./arch/x86/include/asm/cpufeature.h"
extern void setup_clear_cpu_cap(unsigned int bit);
extern void clear_cpu_cap(struct cpuinfo_x86 *c, unsigned int bit);
# 173 "./arch/x86/include/asm/cpufeature.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool _static_cpu_has(u16 bit)
{
 asm goto(
  "# ALT: oldinstr2\n" "661:\n\t" "jmp 6f" "\n662:\n" "# ALT: padding2\n" ".skip -((" "((" "665""1""f-""664""1""f" ") ^ (((" "665""1""f-""664""1""f" ") ^ (" "665""2""f-""664""2""f" ")) & -(-((" "665""1""f-""664""1""f" ") < (" "665""2""f-""664""2""f" ")))))" " - (" "662b-661b" ")) > 0) * " "(" "((" "665""1""f-""664""1""f" ") ^ (((" "665""1""f-""664""1""f" ") ^ (" "665""2""f-""664""2""f" ")) & -(-((" "665""1""f-""664""1""f" ") < (" "665""2""f-""664""2""f" ")))))" " - (" "662b-661b" ")), 0x90\n" "663" ":\n" ".pushsection .altinstructions,\"a\"\n" " .long 661b - .\n" " .long " "664""1""f - .\n" " .4byte " "( 3*32+21)" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""1""f-""664""1""f" "\n" " .long 661b - .\n" " .long " "664""2""f - .\n" " .4byte " "%P[feature]" "\n" " .byte " "663""b-661b" "\n" " .byte " "665""2""f-""664""2""f" "\n" ".popsection\n" ".pushsection .altinstr_replacement, \"ax\"\n" "# ALT: replacement " "1" "\n" "664""1"":\n\t" "jmp %l[t_no]" "\n" "665""1" ":\n" "# ALT: replacement " "2" "\n" "664""2"":\n\t" "" "\n" "665""2" ":\n" ".popsection\n"
  ".pushsection .altinstr_aux,\"ax\"\n"
  "6:\n"
  " testb %[bitnum]," "%P[cap_byte] (%% rip)" "\n"
  " jnz %l[t_yes]\n"
  " jmp %l[t_no]\n"
  ".popsection\n"
   : : [feature] "i" (bit),
       [bitnum] "i" (1 << (bit & 7)),
       [cap_byte] "i" (&((const char *)boot_cpu_data.x86_capability)[bit >> 3])
   : : t_yes, t_no);
t_yes:
 return true;
t_no:
 return false;
}
# 54 "./arch/x86/include/asm/thread_info.h" 2


struct thread_info {
 unsigned long flags;
 unsigned long syscall_work;
 u32 status;

 u32 cpu;

};
# 171 "./arch/x86/include/asm/thread_info.h"

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int arch_within_stack_frames(const void * const stack,
        const void * const stackend,
        const void *obj, unsigned long len)
{
# 204 "./arch/x86/include/asm/thread_info.h"
 return NOT_STACK;

}
# 235 "./arch/x86/include/asm/thread_info.h"
extern void arch_setup_new_exec(void);
# 61 "./include/linux/thread_info.h" 2







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) long set_restart_fn(struct restart_block *restart,
     long (*fn)(struct restart_block *))
{
 restart->fn = fn;
 do { restart->arch_data = ((struct thread_info *)get_current())->status; } while (0);
 return -516;
}
# 87 "./include/linux/thread_info.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void set_ti_thread_flag(struct thread_info *ti, int flag)
{
 set_bit(flag, (unsigned long *)&ti->flags);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void clear_ti_thread_flag(struct thread_info *ti, int flag)
{
 clear_bit(flag, (unsigned long *)&ti->flags);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void update_ti_thread_flag(struct thread_info *ti, int flag,
      bool value)
{
 if (value)
  set_ti_thread_flag(ti, flag);
 else
  clear_ti_thread_flag(ti, flag);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int test_and_set_ti_thread_flag(struct thread_info *ti, int flag)
{
 return test_and_set_bit(flag, (unsigned long *)&ti->flags);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int test_and_clear_ti_thread_flag(struct thread_info *ti, int flag)
{
 return test_and_clear_bit(flag, (unsigned long *)&ti->flags);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int test_ti_thread_flag(struct thread_info *ti, int flag)
{
 return ((__builtin_constant_p(flag) && __builtin_constant_p((uintptr_t)((unsigned long *)&ti->flags) != (uintptr_t)((void *)0)) && (uintptr_t)((unsigned long *)&ti->flags) != (uintptr_t)((void *)0) && __builtin_constant_p(*(const unsigned long *)((unsigned long *)&ti->flags))) ? const_test_bit(flag, (unsigned long *)&ti->flags) : _test_bit(flag, (unsigned long *)&ti->flags));
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) unsigned long read_ti_thread_flags(struct thread_info *ti)
{
 return ({ do { __attribute__((__noreturn__)) extern void __compiletime_assert_42(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(ti->flags) == sizeof(char) || sizeof(ti->flags) == sizeof(short) || sizeof(ti->flags) == sizeof(int) || sizeof(ti->flags) == sizeof(long)) || sizeof(ti->flags) == sizeof(long long))) __compiletime_assert_42(); } while (0); (*(const volatile typeof( _Generic((ti->flags), char: (char)0, unsigned char: (unsigned char)0, signed char: (signed char)0, unsigned short: (unsigned short)0, signed short: (signed short)0, unsigned int: (unsigned int)0, signed int: (signed int)0, unsigned long: (unsigned long)0, signed long: (signed long)0, unsigned long long: (unsigned long long)0, signed long long: (signed long long)0, default: (ti->flags))) *)&(ti->flags)); });
}
# 182 "./include/linux/thread_info.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) bool tif_need_resched(void)
{
 return arch_test_bit(3,
        (unsigned long *)(&((struct thread_info *)get_current())->flags));
}
# 218 "./include/linux/thread_info.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void check_object_size(const void *ptr, unsigned long n,
         bool to_user)
{ }


extern void __attribute__((__error__("copy source size is too small")))
__bad_copy_from(void);
extern void __attribute__((__error__("copy destination size is too small")))
__bad_copy_to(void);

void __copy_overflow(int size, unsigned long count);

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void copy_overflow(int size, unsigned long count)
{
 if (1)
  __copy_overflow(size, count);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) __attribute__((__warn_unused_result__)) bool
check_copy_size(const void *addr, size_t bytes, bool is_source)
{
 int sz = __builtin_object_size(addr, 0);
 if (__builtin_expect(!!(sz >= 0 && sz < bytes), 0)) {
  if (!__builtin_constant_p(bytes))
   copy_overflow(sz, bytes);
  else if (is_source)
   __bad_copy_from();
  else
   __bad_copy_to();
  return false;
 }
 if (({ int __ret_warn_on = !!(bytes > ((int)(~0U >> 1))); if (__builtin_expect(!!(__ret_warn_on), 0)) do { __auto_type __flags = (1 << 0)|((1 << 1) | ((9) << 8)); ({ asm volatile("43" ": nop\n\t" ".pushsection .discard.instr_begin\n\t" ".long " "43" "b - .\n\t" ".popsection\n\t" : : "i" (43)); }); do { asm __inline volatile("1:\t" ".byte 0x0f, 0x0b" "\n" ".pushsection __bug_table,\"aw\"\n" "2:\t" ".long " "1b" " - ." "\t# bug_entry::bug_addr\n" "\t" ".long " "%c0" " - ." "\t# bug_entry::file\n" "\t.word %c1" "\t# bug_entry::line\n" "\t.word %c2" "\t# bug_entry::flags\n" "\t.org 2b+%c3\n" ".popsection\n" "998:\n\t" ".pushsection .discard.reachable\n\t" ".long 998b\n\t" ".popsection\n\t" : : "i" ("include/linux/thread_info.h"), "i" (249), "i" (__flags), "i" (sizeof(struct bug_entry))); } while (0); ({ asm volatile("44" ": nop\n\t" ".pushsection .discard.instr_end\n\t" ".long " "44" "b - .\n\t" ".popsection\n\t" : : "i" (44)); }); } while (0); __builtin_expect(!!(__ret_warn_on), 0); }))
  return false;
 check_object_size(addr, bytes, is_source);
 return true;
}





void arch_task_cache_init(void);
void arch_release_task_struct(struct task_struct *tsk);
int arch_dup_task_struct(struct task_struct *dst,
    struct task_struct *src);
# 113 "./include/linux/smp.h" 2
# 1 "./arch/x86/include/asm/smp.h" 1
# 11 "./arch/x86/include/asm/smp.h"
extern int smp_num_siblings;
extern unsigned int num_processors;

extern __attribute__((section(".data..percpu" "..read_mostly"))) __typeof__(cpumask_var_t) cpu_sibling_map;
extern __attribute__((section(".data..percpu" "..read_mostly"))) __typeof__(cpumask_var_t) cpu_core_map;
extern __attribute__((section(".data..percpu" "..read_mostly"))) __typeof__(cpumask_var_t) cpu_die_map;

extern __attribute__((section(".data..percpu" "..read_mostly"))) __typeof__(cpumask_var_t) cpu_llc_shared_map;
extern __attribute__((section(".data..percpu" "..read_mostly"))) __typeof__(cpumask_var_t) cpu_l2c_shared_map;

extern __attribute__((section(".data..percpu" "..read_mostly"))) __typeof__(u32) x86_cpu_to_apicid; extern __typeof__(u32) *x86_cpu_to_apicid_early_ptr; extern __typeof__(u32) x86_cpu_to_apicid_early_map[];
extern __attribute__((section(".data..percpu" "..read_mostly"))) __typeof__(u32) x86_cpu_to_acpiid; extern __typeof__(u32) *x86_cpu_to_acpiid_early_ptr; extern __typeof__(u32) x86_cpu_to_acpiid_early_map[];

struct task_struct;

struct smp_ops {
 void (*smp_prepare_boot_cpu)(void);
 void (*smp_prepare_cpus)(unsigned max_cpus);
 void (*smp_cpus_done)(unsigned max_cpus);

 void (*stop_other_cpus)(int wait);
 void (*crash_stop_other_cpus)(void);
 void (*smp_send_reschedule)(int cpu);

 void (*cleanup_dead_cpu)(unsigned cpu);
 void (*poll_sync_state)(void);
 int (*kick_ap_alive)(unsigned cpu, struct task_struct *tidle);
 int (*cpu_disable)(void);
 void (*cpu_die)(unsigned int cpu);
 void (*play_dead)(void);

 void (*send_call_func_ipi)(const struct cpumask *mask);
 void (*send_call_func_single_ipi)(int cpu);
};


extern void set_cpu_sibling_map(int cpu);


extern struct smp_ops smp_ops;

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void smp_send_stop(void)
{
 smp_ops.stop_other_cpus(0);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void stop_other_cpus(void)
{
 smp_ops.stop_other_cpus(1);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void smp_prepare_boot_cpu(void)
{
 smp_ops.smp_prepare_boot_cpu();
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void smp_prepare_cpus(unsigned int max_cpus)
{
 smp_ops.smp_prepare_cpus(max_cpus);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void smp_cpus_done(unsigned int max_cpus)
{
 smp_ops.smp_cpus_done(max_cpus);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int __cpu_disable(void)
{
 return smp_ops.cpu_disable();
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __cpu_die(unsigned int cpu)
{
 if (smp_ops.cpu_die)
  smp_ops.cpu_die(cpu);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void __attribute__((__noreturn__)) play_dead(void)
{
 smp_ops.play_dead();
 do { ({ asm volatile("45" ": nop\n\t" ".pushsection .discard.instr_begin\n\t" ".long " "45" "b - .\n\t" ".popsection\n\t" : : "i" (45)); }); do { asm __inline volatile("1:\t" ".byte 0x0f, 0x0b" "\n" ".pushsection __bug_table,\"aw\"\n" "2:\t" ".long " "1b" " - ." "\t# bug_entry::bug_addr\n" "\t" ".long " "%c0" " - ." "\t# bug_entry::file\n" "\t.word %c1" "\t# bug_entry::line\n" "\t.word %c2" "\t# bug_entry::flags\n" "\t.org 2b+%c3\n" ".popsection\n" "" : : "i" ("arch/x86/include/asm/smp.h"), "i" (91), "i" (0), "i" (sizeof(struct bug_entry))); } while (0); __builtin_unreachable(); } while (0);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void arch_smp_send_reschedule(int cpu)
{
 smp_ops.smp_send_reschedule(cpu);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void arch_send_call_function_single_ipi(int cpu)
{
 smp_ops.send_call_func_single_ipi(cpu);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void arch_send_call_function_ipi_mask(const struct cpumask *mask)
{
 smp_ops.send_call_func_ipi(mask);
}

void cpu_disable_common(void);
void native_smp_prepare_boot_cpu(void);
void smp_prepare_cpus_common(void);
void native_smp_prepare_cpus(unsigned int max_cpus);
void calculate_max_logical_packages(void);
void native_smp_cpus_done(unsigned int max_cpus);
int common_cpu_up(unsigned int cpunum, struct task_struct *tidle);
int native_kick_ap(unsigned int cpu, struct task_struct *tidle);
int native_cpu_disable(void);
void __attribute__((__noreturn__)) hlt_play_dead(void);
void native_play_dead(void);
void play_dead_common(void);
void wbinvd_on_cpu(int cpu);
int wbinvd_on_all_cpus(void);

void smp_kick_mwait_play_dead(void);

void native_smp_send_reschedule(int cpu);
void native_send_call_func_ipi(const struct cpumask *mask);
void native_send_call_func_single_ipi(int cpu);

void smp_store_cpu_info(int id);

 __attribute__((__externally_visible__)) void smp_reboot_interrupt(void);
__attribute__((__externally_visible__)) void smp_reschedule_interrupt(struct pt_regs *regs);
__attribute__((__externally_visible__)) void smp_call_function_interrupt(struct pt_regs *regs);
__attribute__((__externally_visible__)) void smp_call_function_single_interrupt(struct pt_regs *r);
# 153 "./arch/x86/include/asm/smp.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) struct cpumask *cpu_llc_shared_mask(int cpu)
{
 return (*({ do { const void *__vpp_verify = (typeof((&(cpu_llc_shared_map)) + 0))((void *)0); (void)__vpp_verify; } while (0); ({ unsigned long __ptr; __asm__ ("" : "=r"(__ptr) : "0"((typeof(*((&(cpu_llc_shared_map)))) *)((&(cpu_llc_shared_map))))); (typeof((typeof(*((&(cpu_llc_shared_map)))) *)((&(cpu_llc_shared_map))))) (__ptr + (((__per_cpu_offset[(cpu)])))); }); }));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) struct cpumask *cpu_l2c_shared_mask(int cpu)
{
 return (*({ do { const void *__vpp_verify = (typeof((&(cpu_l2c_shared_map)) + 0))((void *)0); (void)__vpp_verify; } while (0); ({ unsigned long __ptr; __asm__ ("" : "=r"(__ptr) : "0"((typeof(*((&(cpu_l2c_shared_map)))) *)((&(cpu_l2c_shared_map))))); (typeof((typeof(*((&(cpu_l2c_shared_map)))) *)((&(cpu_l2c_shared_map))))) (__ptr + (((__per_cpu_offset[(cpu)])))); }); }));
}
# 177 "./arch/x86/include/asm/smp.h"
extern unsigned disabled_cpus;







extern unsigned int smpboot_control;
extern unsigned long apic_mmio_base;
# 114 "./include/linux/smp.h" 2
# 123 "./include/linux/smp.h"
extern void smp_send_stop(void);




extern void arch_smp_send_reschedule(int cpu);
# 141 "./include/linux/smp.h"
extern void smp_prepare_cpus(unsigned int max_cpus);




extern int __cpu_up(unsigned int cpunum, struct task_struct *tidle);




extern void smp_cpus_done(unsigned int max_cpus);




void smp_call_function(smp_call_func_t func, void *info, int wait);
void smp_call_function_many(const struct cpumask *mask,
       smp_call_func_t func, void *info, bool wait);

int smp_call_function_any(const struct cpumask *mask,
     smp_call_func_t func, void *info, int wait);

void kick_all_cpus_sync(void);
void wake_up_all_idle_cpus(void);




void __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep"))) call_function_init(void);
void generic_smp_call_function_single_interrupt(void);







void smp_prepare_boot_cpu(void);

extern unsigned int setup_max_cpus;
extern void __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep"))) setup_nr_cpu_ids(void);
extern void __attribute__((__section__(".init.text"))) __attribute__((__indirect_branch__("keep"))) smp_init(void);

extern int __boot_cpu_id;

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int get_boot_cpu_id(void)
{
 return __boot_cpu_id;
}
# 281 "./include/linux/smp.h"
extern void arch_disable_smp_support(void);

extern void arch_thaw_secondary_cpus_begin(void);
extern void arch_thaw_secondary_cpus_end(void);

void smp_setup_processor_id(void);

int smp_call_on_cpu(unsigned int cpu, int (*func)(void *), void *par,
      bool phys);


int smpcfd_prepare_cpu(unsigned int cpu);
int smpcfd_dead_cpu(unsigned int cpu);
int smpcfd_dying_cpu(unsigned int cpu);
# 15 "./include/linux/lockdep.h" 2


struct task_struct;
# 302 "./include/linux/lockdep.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void lockdep_init_task(struct task_struct *task)
{
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void lockdep_off(void)
{
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void lockdep_on(void)
{
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void lockdep_set_selftest_task(struct task_struct *task)
{
}
# 352 "./include/linux/lockdep.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void lockdep_register_key(struct lock_class_key *key)
{
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void lockdep_unregister_key(struct lock_class_key *key)
{
}







extern int lock_is_held(const void *);
extern int lockdep_is_held(const void *);
# 401 "./include/linux/lockdep.h"
enum xhlock_context_t {
 XHLOCK_HARD,
 XHLOCK_SOFT,
 XHLOCK_CTX_NR,
};
# 414 "./include/linux/lockdep.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void lockdep_invariant_state(bool force) {}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void lockdep_free_task(struct task_struct *task) {}
# 459 "./include/linux/lockdep.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void print_irqtrace_events(struct task_struct *curr)
{
}
# 636 "./include/linux/lockdep.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void
lockdep_rcu_suspicious(const char *file, const int line, const char *s)
{
}
# 30 "./include/linux/rcupdate.h" 2



# 1 "./include/linux/context_tracking_irq.h" 1





void ct_irq_enter(void);
void ct_irq_exit(void);
void ct_irq_enter_irqson(void);
void ct_irq_exit_irqson(void);
void ct_nmi_enter(void);
void ct_nmi_exit(void);
# 34 "./include/linux/rcupdate.h" 2





void call_rcu(struct callback_head *head, rcu_callback_t func);
void rcu_barrier_tasks(void);
void rcu_barrier_tasks_rude(void);
void synchronize_rcu(void);

struct rcu_gp_oldstate;
unsigned long get_completed_synchronize_rcu(void);
void get_completed_synchronize_rcu_full(struct rcu_gp_oldstate *rgosp);
# 64 "./include/linux/rcupdate.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool same_state_synchronize_rcu(unsigned long oldstate1, unsigned long oldstate2)
{
 return oldstate1 == oldstate2;
}



void __rcu_read_lock(void);
void __rcu_read_unlock(void);
# 112 "./include/linux/rcupdate.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void call_rcu_hurry(struct callback_head *head, rcu_callback_t func)
{
 call_rcu(head, func);
}



void rcu_init(void);
extern int rcu_scheduler_active;
void rcu_sched_clock_irq(int user);


void rcu_init_tasks_generic(void);





void rcu_sysrq_start(void);
void rcu_sysrq_end(void);
# 140 "./include/linux/rcupdate.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rcu_irq_work_resched(void) { }
# 149 "./include/linux/rcupdate.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rcu_init_nohz(void) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int rcu_nocb_cpu_offload(int cpu) { return -22; }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int rcu_nocb_cpu_deoffload(int cpu) { return 0; }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rcu_nocb_flush_deferred_wakeup(void) { }
# 167 "./include/linux/rcupdate.h"
void call_rcu_tasks(struct callback_head *head, rcu_callback_t func);
void synchronize_rcu_tasks(void);
# 211 "./include/linux/rcupdate.h"
void exit_tasks_rcu_start(void);
void exit_tasks_rcu_stop(void);
void exit_tasks_rcu_finish(void);
# 235 "./include/linux/rcupdate.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool rcu_trace_implies_rcu_gp(void) { return true; }
# 287 "./include/linux/rcupdate.h"
# 1 "./include/linux/rcutree.h" 1
# 20 "./include/linux/rcutree.h"
void rcu_softirq_qs(void);
void rcu_note_context_switch(bool preempt);
int rcu_needs_cpu(void);
void rcu_cpu_stall_reset(void);
void rcu_request_urgent_qs_task(struct task_struct *t);






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rcu_virt_note_context_switch(void)
{
 rcu_note_context_switch(false);
}

void synchronize_rcu_expedited(void);
void kvfree_call_rcu(struct callback_head *head, void *ptr);

void rcu_barrier(void);
void rcu_momentary_dyntick_idle(void);
void kfree_rcu_scheduler_running(void);
bool rcu_gp_might_be_stalled(void);

struct rcu_gp_oldstate {
 unsigned long rgos_norm;
 unsigned long rgos_exp;
};
# 71 "./include/linux/rcutree.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool same_state_synchronize_rcu_full(struct rcu_gp_oldstate *rgosp1,
         struct rcu_gp_oldstate *rgosp2)
{
 return rgosp1->rgos_norm == rgosp2->rgos_norm && rgosp1->rgos_exp == rgosp2->rgos_exp;
}

unsigned long start_poll_synchronize_rcu_expedited(void);
void start_poll_synchronize_rcu_expedited_full(struct rcu_gp_oldstate *rgosp);
void cond_synchronize_rcu_expedited(unsigned long oldstate);
void cond_synchronize_rcu_expedited_full(struct rcu_gp_oldstate *rgosp);
unsigned long get_state_synchronize_rcu(void);
void get_state_synchronize_rcu_full(struct rcu_gp_oldstate *rgosp);
unsigned long start_poll_synchronize_rcu(void);
void start_poll_synchronize_rcu_full(struct rcu_gp_oldstate *rgosp);
bool poll_state_synchronize_rcu(unsigned long oldstate);
bool poll_state_synchronize_rcu_full(struct rcu_gp_oldstate *rgosp);
void cond_synchronize_rcu(unsigned long oldstate);
void cond_synchronize_rcu_full(struct rcu_gp_oldstate *rgosp);




static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rcu_irq_exit_check_preempt(void) { }


struct task_struct;
void rcu_preempt_deferred_qs(struct task_struct *t);

void exit_rcu(void);

void rcu_scheduler_starting(void);
extern int rcu_scheduler_active;
void rcu_end_inkernel_boot(void);
bool rcu_inkernel_boot_has_ended(void);
bool rcu_is_watching(void);





int rcutree_prepare_cpu(unsigned int cpu);
int rcutree_online_cpu(unsigned int cpu);
void rcutree_report_cpu_starting(unsigned int cpu);


int rcutree_dead_cpu(unsigned int cpu);
int rcutree_dying_cpu(unsigned int cpu);
int rcutree_offline_cpu(unsigned int cpu);






void rcutree_migrate_callbacks(int cpu);


void rcutree_report_cpu_dead(void);
# 288 "./include/linux/rcupdate.h" 2
# 308 "./include/linux/rcupdate.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void init_rcu_head(struct callback_head *head) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void destroy_rcu_head(struct callback_head *head) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void init_rcu_head_on_stack(struct callback_head *head) { }
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void destroy_rcu_head_on_stack(struct callback_head *head) { }





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool rcu_lockdep_current_cpu_online(void) { return true; }


extern struct lockdep_map rcu_lock_map;
extern struct lockdep_map rcu_bh_lock_map;
extern struct lockdep_map rcu_sched_lock_map;
extern struct lockdep_map rcu_callback_map;
# 354 "./include/linux/rcupdate.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int rcu_read_lock_held(void)
{
 return 1;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int rcu_read_lock_bh_held(void)
{
 return 1;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int rcu_read_lock_sched_held(void)
{
 return !(preempt_count() == 0 && !({ unsigned long _flags; do { ({ unsigned long __dummy; typeof(_flags) __dummy2; (void)(&__dummy == &__dummy2); 1; }); _flags = arch_local_save_flags(); } while (0); ({ ({ unsigned long __dummy; typeof(_flags) __dummy2; (void)(&__dummy == &__dummy2); 1; }); arch_irqs_disabled_flags(_flags); }); }));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int rcu_read_lock_any_held(void)
{
 return !(preempt_count() == 0 && !({ unsigned long _flags; do { ({ unsigned long __dummy; typeof(_flags) __dummy2; (void)(&__dummy == &__dummy2); 1; }); _flags = arch_local_save_flags(); } while (0); ({ ({ unsigned long __dummy; typeof(_flags) __dummy2; (void)(&__dummy == &__dummy2); 1; }); arch_irqs_disabled_flags(_flags); }); }));
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int debug_lockdep_rcu_enabled(void)
{
 return 0;
}
# 777 "./include/linux/rcupdate.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void rcu_read_lock(void)
{
 __rcu_read_lock();
 (void)0;
 do { } while (0);
 do { } while (0 && (!rcu_is_watching()))
                                                ;
}
# 808 "./include/linux/rcupdate.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rcu_read_unlock(void)
{
 do { } while (0 && (!rcu_is_watching()))
                                                  ;
 (void)0;
 __rcu_read_unlock();
 do { } while (0);
}
# 831 "./include/linux/rcupdate.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rcu_read_lock_bh(void)
{
 local_bh_disable();
 (void)0;
 do { } while (0);
 do { } while (0 && (!rcu_is_watching()))
                                                   ;
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rcu_read_unlock_bh(void)
{
 do { } while (0 && (!rcu_is_watching()))
                                                     ;
 do { } while (0);
 (void)0;
 local_bh_enable();
}
# 869 "./include/linux/rcupdate.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rcu_read_lock_sched(void)
{
 do { __preempt_count_add(1); __asm__ __volatile__("": : :"memory"); } while (0);
 (void)0;
 do { } while (0);
 do { } while (0 && (!rcu_is_watching()))
                                                      ;
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((no_instrument_function)) void rcu_read_lock_sched_notrace(void)
{
 do { __preempt_count_add(1); __asm__ __volatile__("": : :"memory"); } while (0);
 (void)0;
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rcu_read_unlock_sched(void)
{
 do { } while (0 && (!rcu_is_watching()))
                                                        ;
 do { } while (0);
 (void)0;
 do { __asm__ __volatile__("": : :"memory"); if (__builtin_expect(!!(__preempt_count_dec_and_test()), 0)) do { static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable___SCK__preempt_schedule46 = (void *)&__SCK__preempt_schedule;; asm volatile ("call " "__SCT__preempt_schedule" : "+r" (current_stack_pointer)); } while (0); } while (0);
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((no_instrument_function)) void rcu_read_unlock_sched_notrace(void)
{
 (void)0;
 do { __asm__ __volatile__("": : :"memory"); if (__builtin_expect(!!(__preempt_count_dec_and_test()), 0)) do { static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable___SCK__preempt_schedule_notrace47 = (void *)&__SCK__preempt_schedule_notrace;; asm volatile ("call " "__SCT__preempt_schedule_notrace" : "+r" (current_stack_pointer)); } while (0); } while (0);
}
# 1060 "./include/linux/rcupdate.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rcu_head_init(struct callback_head *rhp)
{
 rhp->func = (rcu_callback_t)~0L;
}
# 1078 "./include/linux/rcupdate.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) bool
rcu_head_after_call_rcu(struct callback_head *rhp, rcu_callback_t f)
{
 rcu_callback_t func = ({ do { __attribute__((__noreturn__)) extern void __compiletime_assert_48(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(rhp->func) == sizeof(char) || sizeof(rhp->func) == sizeof(short) || sizeof(rhp->func) == sizeof(int) || sizeof(rhp->func) == sizeof(long)) || sizeof(rhp->func) == sizeof(long long))) __compiletime_assert_48(); } while (0); (*(const volatile typeof( _Generic((rhp->func), char: (char)0, unsigned char: (unsigned char)0, signed char: (signed char)0, unsigned short: (unsigned short)0, signed short: (signed short)0, unsigned int: (unsigned int)0, signed int: (signed int)0, unsigned long: (unsigned long)0, signed long: (signed long)0, unsigned long long: (unsigned long long)0, signed long long: (signed long long)0, default: (rhp->func))) *)&(rhp->func)); });

 if (func == f)
  return true;
 ({ int __ret_warn_on = !!(func != (rcu_callback_t)~0L); if (__builtin_expect(!!(__ret_warn_on), 0)) do { __auto_type __flags = (1 << 0)|((1 << 1) | ((9) << 8)); ({ asm volatile("49" ": nop\n\t" ".pushsection .discard.instr_begin\n\t" ".long " "49" "b - .\n\t" ".popsection\n\t" : : "i" (49)); }); do { asm __inline volatile("1:\t" ".byte 0x0f, 0x0b" "\n" ".pushsection __bug_table,\"aw\"\n" "2:\t" ".long " "1b" " - ." "\t# bug_entry::bug_addr\n" "\t" ".long " "%c0" " - ." "\t# bug_entry::file\n" "\t.word %c1" "\t# bug_entry::line\n" "\t.word %c2" "\t# bug_entry::flags\n" "\t.org 2b+%c3\n" ".popsection\n" "998:\n\t" ".pushsection .discard.reachable\n\t" ".long 998b\n\t" ".popsection\n\t" : : "i" ("include/linux/rcupdate.h"), "i" (1085), "i" (__flags), "i" (sizeof(struct bug_entry))); } while (0); ({ asm volatile("50" ": nop\n\t" ".pushsection .discard.instr_end\n\t" ".long " "50" "b - .\n\t" ".popsection\n\t" : : "i" (50)); }); } while (0); __builtin_expect(!!(__ret_warn_on), 0); });
 return false;
}


extern int rcu_expedited;
extern int rcu_normal;

typedef struct { void *lock; ; } class_rcu_t; static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void class_rcu_destructor(class_rcu_t *_T) { if (_T->lock) { rcu_read_unlock(); } } static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void *class_rcu_lock_ptr(class_rcu_t *_T) { return _T->lock; } static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) class_rcu_t class_rcu_constructor(void) { class_rcu_t _t = { .lock = (void*)1 }, *_T __attribute__((__unused__)) = &_t; rcu_read_lock(); return _t; }
# 25 "./include/linux/rbtree.h" 2
# 39 "./include/linux/rbtree.h"
extern void rb_insert_color(struct rb_node *, struct rb_root *);
extern void rb_erase(struct rb_node *, struct rb_root *);



extern struct rb_node *rb_next(const struct rb_node *);
extern struct rb_node *rb_prev(const struct rb_node *);
extern struct rb_node *rb_first(const struct rb_root *);
extern struct rb_node *rb_last(const struct rb_root *);


extern struct rb_node *rb_first_postorder(const struct rb_root *);
extern struct rb_node *rb_next_postorder(const struct rb_node *);


extern void rb_replace_node(struct rb_node *victim, struct rb_node *new,
       struct rb_root *root);
extern void rb_replace_node_rcu(struct rb_node *victim, struct rb_node *new,
    struct rb_root *root);

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rb_link_node(struct rb_node *node, struct rb_node *parent,
    struct rb_node **rb_link)
{
 node->__rb_parent_color = (unsigned long)parent;
 node->rb_left = node->rb_right = ((void *)0);

 *rb_link = node;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rb_link_node_rcu(struct rb_node *node, struct rb_node *parent,
        struct rb_node **rb_link)
{
 node->__rb_parent_color = (unsigned long)parent;
 node->rb_left = node->rb_right = ((void *)0);

 do { uintptr_t _r_a_p__v = (uintptr_t)(node); ; if (__builtin_constant_p(node) && (_r_a_p__v) == (uintptr_t)((void *)0)) do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_51(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof((*rb_link)) == sizeof(char) || sizeof((*rb_link)) == sizeof(short) || sizeof((*rb_link)) == sizeof(int) || sizeof((*rb_link)) == sizeof(long)) || sizeof((*rb_link)) == sizeof(long long))) __compiletime_assert_51(); } while (0); do { *(volatile typeof((*rb_link)) *)&((*rb_link)) = ((typeof(*rb_link))(_r_a_p__v)); } while (0); } while (0); else do { do { } while (0); do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_52(void) __attribute__((__error__("Need native word sized stores/loads for atomicity."))); if (!((sizeof(*&*rb_link) == sizeof(char) || sizeof(*&*rb_link) == sizeof(short) || sizeof(*&*rb_link) == sizeof(int) || sizeof(*&*rb_link) == sizeof(long)))) __compiletime_assert_52(); } while (0); __asm__ __volatile__("": : :"memory"); do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_53(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(*&*rb_link) == sizeof(char) || sizeof(*&*rb_link) == sizeof(short) || sizeof(*&*rb_link) == sizeof(int) || sizeof(*&*rb_link) == sizeof(long)) || sizeof(*&*rb_link) == sizeof(long long))) __compiletime_assert_53(); } while (0); do { *(volatile typeof(*&*rb_link) *)&(*&*rb_link) = ((typeof(*((typeof(*rb_link))_r_a_p__v)) *)((typeof(*rb_link))_r_a_p__v)); } while (0); } while (0); } while (0); } while (0); } while (0);
}
# 108 "./include/linux/rbtree.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rb_insert_color_cached(struct rb_node *node,
       struct rb_root_cached *root,
       bool leftmost)
{
 if (leftmost)
  root->rb_leftmost = node;
 rb_insert_color(node, &root->rb_root);
}


static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) struct rb_node *
rb_erase_cached(struct rb_node *node, struct rb_root_cached *root)
{
 struct rb_node *leftmost = ((void *)0);

 if (root->rb_leftmost == node)
  leftmost = root->rb_leftmost = rb_next(node);

 rb_erase(node, &root->rb_root);

 return leftmost;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rb_replace_node_cached(struct rb_node *victim,
       struct rb_node *new,
       struct rb_root_cached *root)
{
 if (root->rb_leftmost == victim)
  root->rb_leftmost = new;
 rb_replace_node(victim, new, &root->rb_root);
}
# 164 "./include/linux/rbtree.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) struct rb_node *
rb_add_cached(struct rb_node *node, struct rb_root_cached *tree,
       bool (*less)(struct rb_node *, const struct rb_node *))
{
 struct rb_node **link = &tree->rb_root.rb_node;
 struct rb_node *parent = ((void *)0);
 bool leftmost = true;

 while (*link) {
  parent = *link;
  if (less(node, parent)) {
   link = &parent->rb_left;
  } else {
   link = &parent->rb_right;
   leftmost = false;
  }
 }

 rb_link_node(node, parent, link);
 rb_insert_color_cached(node, tree, leftmost);

 return leftmost ? node : ((void *)0);
}







static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
rb_add(struct rb_node *node, struct rb_root *tree,
       bool (*less)(struct rb_node *, const struct rb_node *))
{
 struct rb_node **link = &tree->rb_node;
 struct rb_node *parent = ((void *)0);

 while (*link) {
  parent = *link;
  if (less(node, parent))
   link = &parent->rb_left;
  else
   link = &parent->rb_right;
 }

 rb_link_node(node, parent, link);
 rb_insert_color(node, tree);
}
# 222 "./include/linux/rbtree.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) struct rb_node *
rb_find_add(struct rb_node *node, struct rb_root *tree,
     int (*cmp)(struct rb_node *, const struct rb_node *))
{
 struct rb_node **link = &tree->rb_node;
 struct rb_node *parent = ((void *)0);
 int c;

 while (*link) {
  parent = *link;
  c = cmp(node, parent);

  if (c < 0)
   link = &parent->rb_left;
  else if (c > 0)
   link = &parent->rb_right;
  else
   return parent;
 }

 rb_link_node(node, parent, link);
 rb_insert_color(node, tree);
 return ((void *)0);
}
# 255 "./include/linux/rbtree.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) struct rb_node *
rb_find(const void *key, const struct rb_root *tree,
 int (*cmp)(const void *key, const struct rb_node *))
{
 struct rb_node *node = tree->rb_node;

 while (node) {
  int c = cmp(key, node);

  if (c < 0)
   node = node->rb_left;
  else if (c > 0)
   node = node->rb_right;
  else
   return node;
 }

 return ((void *)0);
}
# 283 "./include/linux/rbtree.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) struct rb_node *
rb_find_first(const void *key, const struct rb_root *tree,
       int (*cmp)(const void *key, const struct rb_node *))
{
 struct rb_node *node = tree->rb_node;
 struct rb_node *match = ((void *)0);

 while (node) {
  int c = cmp(key, node);

  if (c <= 0) {
   if (!c)
    match = node;
   node = node->rb_left;
  } else if (c > 0) {
   node = node->rb_right;
  }
 }

 return match;
}
# 313 "./include/linux/rbtree.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) struct rb_node *
rb_next_match(const void *key, struct rb_node *node,
       int (*cmp)(const void *key, const struct rb_node *))
{
 node = rb_next(node);
 if (node && cmp(key, node))
  node = ((void *)0);
 return node;
}
# 17 "./include/linux/rbtree_augmented.h" 2
# 27 "./include/linux/rbtree_augmented.h"
struct rb_augment_callbacks {
 void (*propagate)(struct rb_node *node, struct rb_node *stop);
 void (*copy)(struct rb_node *old, struct rb_node *new);
 void (*rotate)(struct rb_node *old, struct rb_node *new);
};

extern void __rb_insert_augmented(struct rb_node *node, struct rb_root *root,
 void (*augment_rotate)(struct rb_node *old, struct rb_node *new));
# 46 "./include/linux/rbtree_augmented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void
rb_insert_augmented(struct rb_node *node, struct rb_root *root,
      const struct rb_augment_callbacks *augment)
{
 __rb_insert_augmented(node, root, augment->rotate);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void
rb_insert_augmented_cached(struct rb_node *node,
      struct rb_root_cached *root, bool newleft,
      const struct rb_augment_callbacks *augment)
{
 if (newleft)
  root->rb_leftmost = node;
 rb_insert_augmented(node, &root->rb_root, augment);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) struct rb_node *
rb_add_augmented_cached(struct rb_node *node, struct rb_root_cached *tree,
   bool (*less)(struct rb_node *, const struct rb_node *),
   const struct rb_augment_callbacks *augment)
{
 struct rb_node **link = &tree->rb_root.rb_node;
 struct rb_node *parent = ((void *)0);
 bool leftmost = true;

 while (*link) {
  parent = *link;
  if (less(node, parent)) {
   link = &parent->rb_left;
  } else {
   link = &parent->rb_right;
   leftmost = false;
  }
 }

 rb_link_node(node, parent, link);
 augment->propagate(parent, ((void *)0));
 rb_insert_augmented_cached(node, tree, leftmost, augment);

 return leftmost ? node : ((void *)0);
}
# 183 "./include/linux/rbtree_augmented.h"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rb_set_parent(struct rb_node *rb, struct rb_node *p)
{
 rb->__rb_parent_color = (((rb)->__rb_parent_color) & 1) + (unsigned long)p;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rb_set_parent_color(struct rb_node *rb,
           struct rb_node *p, int color)
{
 rb->__rb_parent_color = (unsigned long)p + color;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void
__rb_change_child(struct rb_node *old, struct rb_node *new,
    struct rb_node *parent, struct rb_root *root)
{
 if (parent) {
  if (parent->rb_left == old)
   do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_54(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(parent->rb_left) == sizeof(char) || sizeof(parent->rb_left) == sizeof(short) || sizeof(parent->rb_left) == sizeof(int) || sizeof(parent->rb_left) == sizeof(long)) || sizeof(parent->rb_left) == sizeof(long long))) __compiletime_assert_54(); } while (0); do { *(volatile typeof(parent->rb_left) *)&(parent->rb_left) = (new); } while (0); } while (0);
  else
   do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_55(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(parent->rb_right) == sizeof(char) || sizeof(parent->rb_right) == sizeof(short) || sizeof(parent->rb_right) == sizeof(int) || sizeof(parent->rb_right) == sizeof(long)) || sizeof(parent->rb_right) == sizeof(long long))) __compiletime_assert_55(); } while (0); do { *(volatile typeof(parent->rb_right) *)&(parent->rb_right) = (new); } while (0); } while (0);
 } else
  do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_56(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(root->rb_node) == sizeof(char) || sizeof(root->rb_node) == sizeof(short) || sizeof(root->rb_node) == sizeof(int) || sizeof(root->rb_node) == sizeof(long)) || sizeof(root->rb_node) == sizeof(long long))) __compiletime_assert_56(); } while (0); do { *(volatile typeof(root->rb_node) *)&(root->rb_node) = (new); } while (0); } while (0);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void
__rb_change_child_rcu(struct rb_node *old, struct rb_node *new,
        struct rb_node *parent, struct rb_root *root)
{
 if (parent) {
  if (parent->rb_left == old)
   do { uintptr_t _r_a_p__v = (uintptr_t)(new); ; if (__builtin_constant_p(new) && (_r_a_p__v) == (uintptr_t)((void *)0)) do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_57(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof((parent->rb_left)) == sizeof(char) || sizeof((parent->rb_left)) == sizeof(short) || sizeof((parent->rb_left)) == sizeof(int) || sizeof((parent->rb_left)) == sizeof(long)) || sizeof((parent->rb_left)) == sizeof(long long))) __compiletime_assert_57(); } while (0); do { *(volatile typeof((parent->rb_left)) *)&((parent->rb_left)) = ((typeof(parent->rb_left))(_r_a_p__v)); } while (0); } while (0); else do { do { } while (0); do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_58(void) __attribute__((__error__("Need native word sized stores/loads for atomicity."))); if (!((sizeof(*&parent->rb_left) == sizeof(char) || sizeof(*&parent->rb_left) == sizeof(short) || sizeof(*&parent->rb_left) == sizeof(int) || sizeof(*&parent->rb_left) == sizeof(long)))) __compiletime_assert_58(); } while (0); __asm__ __volatile__("": : :"memory"); do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_59(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(*&parent->rb_left) == sizeof(char) || sizeof(*&parent->rb_left) == sizeof(short) || sizeof(*&parent->rb_left) == sizeof(int) || sizeof(*&parent->rb_left) == sizeof(long)) || sizeof(*&parent->rb_left) == sizeof(long long))) __compiletime_assert_59(); } while (0); do { *(volatile typeof(*&parent->rb_left) *)&(*&parent->rb_left) = ((typeof(*((typeof(parent->rb_left))_r_a_p__v)) *)((typeof(parent->rb_left))_r_a_p__v)); } while (0); } while (0); } while (0); } while (0); } while (0);
  else
   do { uintptr_t _r_a_p__v = (uintptr_t)(new); ; if (__builtin_constant_p(new) && (_r_a_p__v) == (uintptr_t)((void *)0)) do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_60(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof((parent->rb_right)) == sizeof(char) || sizeof((parent->rb_right)) == sizeof(short) || sizeof((parent->rb_right)) == sizeof(int) || sizeof((parent->rb_right)) == sizeof(long)) || sizeof((parent->rb_right)) == sizeof(long long))) __compiletime_assert_60(); } while (0); do { *(volatile typeof((parent->rb_right)) *)&((parent->rb_right)) = ((typeof(parent->rb_right))(_r_a_p__v)); } while (0); } while (0); else do { do { } while (0); do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_61(void) __attribute__((__error__("Need native word sized stores/loads for atomicity."))); if (!((sizeof(*&parent->rb_right) == sizeof(char) || sizeof(*&parent->rb_right) == sizeof(short) || sizeof(*&parent->rb_right) == sizeof(int) || sizeof(*&parent->rb_right) == sizeof(long)))) __compiletime_assert_61(); } while (0); __asm__ __volatile__("": : :"memory"); do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_62(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(*&parent->rb_right) == sizeof(char) || sizeof(*&parent->rb_right) == sizeof(short) || sizeof(*&parent->rb_right) == sizeof(int) || sizeof(*&parent->rb_right) == sizeof(long)) || sizeof(*&parent->rb_right) == sizeof(long long))) __compiletime_assert_62(); } while (0); do { *(volatile typeof(*&parent->rb_right) *)&(*&parent->rb_right) = ((typeof(*((typeof(parent->rb_right))_r_a_p__v)) *)((typeof(parent->rb_right))_r_a_p__v)); } while (0); } while (0); } while (0); } while (0); } while (0);
 } else
  do { uintptr_t _r_a_p__v = (uintptr_t)(new); ; if (__builtin_constant_p(new) && (_r_a_p__v) == (uintptr_t)((void *)0)) do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_63(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof((root->rb_node)) == sizeof(char) || sizeof((root->rb_node)) == sizeof(short) || sizeof((root->rb_node)) == sizeof(int) || sizeof((root->rb_node)) == sizeof(long)) || sizeof((root->rb_node)) == sizeof(long long))) __compiletime_assert_63(); } while (0); do { *(volatile typeof((root->rb_node)) *)&((root->rb_node)) = ((typeof(root->rb_node))(_r_a_p__v)); } while (0); } while (0); else do { do { } while (0); do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_64(void) __attribute__((__error__("Need native word sized stores/loads for atomicity."))); if (!((sizeof(*&root->rb_node) == sizeof(char) || sizeof(*&root->rb_node) == sizeof(short) || sizeof(*&root->rb_node) == sizeof(int) || sizeof(*&root->rb_node) == sizeof(long)))) __compiletime_assert_64(); } while (0); __asm__ __volatile__("": : :"memory"); do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_65(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(*&root->rb_node) == sizeof(char) || sizeof(*&root->rb_node) == sizeof(short) || sizeof(*&root->rb_node) == sizeof(int) || sizeof(*&root->rb_node) == sizeof(long)) || sizeof(*&root->rb_node) == sizeof(long long))) __compiletime_assert_65(); } while (0); do { *(volatile typeof(*&root->rb_node) *)&(*&root->rb_node) = ((typeof(*((typeof(root->rb_node))_r_a_p__v)) *)((typeof(root->rb_node))_r_a_p__v)); } while (0); } while (0); } while (0); } while (0); } while (0);
}

extern void __rb_erase_color(struct rb_node *parent, struct rb_root *root,
 void (*augment_rotate)(struct rb_node *old, struct rb_node *new));

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) struct rb_node *
__rb_erase_augmented(struct rb_node *node, struct rb_root *root,
       const struct rb_augment_callbacks *augment)
{
 struct rb_node *child = node->rb_right;
 struct rb_node *tmp = node->rb_left;
 struct rb_node *parent, *rebalance;
 unsigned long pc;

 if (!tmp) {







  pc = node->__rb_parent_color;
  parent = ((struct rb_node *)(pc & ~3));
  __rb_change_child(node, child, parent, root);
  if (child) {
   child->__rb_parent_color = pc;
   rebalance = ((void *)0);
  } else
   rebalance = ((pc) & 1) ? parent : ((void *)0);
  tmp = parent;
 } else if (!child) {

  tmp->__rb_parent_color = pc = node->__rb_parent_color;
  parent = ((struct rb_node *)(pc & ~3));
  __rb_change_child(node, tmp, parent, root);
  rebalance = ((void *)0);
  tmp = parent;
 } else {
  struct rb_node *successor = child, *child2;

  tmp = child->rb_left;
  if (!tmp) {
# 270 "./include/linux/rbtree_augmented.h"
   parent = successor;
   child2 = successor->rb_right;

   augment->copy(node, successor);
  } else {
# 289 "./include/linux/rbtree_augmented.h"
   do {
    parent = successor;
    successor = tmp;
    tmp = tmp->rb_left;
   } while (tmp);
   child2 = successor->rb_right;
   do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_66(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(parent->rb_left) == sizeof(char) || sizeof(parent->rb_left) == sizeof(short) || sizeof(parent->rb_left) == sizeof(int) || sizeof(parent->rb_left) == sizeof(long)) || sizeof(parent->rb_left) == sizeof(long long))) __compiletime_assert_66(); } while (0); do { *(volatile typeof(parent->rb_left) *)&(parent->rb_left) = (child2); } while (0); } while (0);
   do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_67(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(successor->rb_right) == sizeof(char) || sizeof(successor->rb_right) == sizeof(short) || sizeof(successor->rb_right) == sizeof(int) || sizeof(successor->rb_right) == sizeof(long)) || sizeof(successor->rb_right) == sizeof(long long))) __compiletime_assert_67(); } while (0); do { *(volatile typeof(successor->rb_right) *)&(successor->rb_right) = (child); } while (0); } while (0);
   rb_set_parent(child, successor);

   augment->copy(node, successor);
   augment->propagate(parent, successor);
  }

  tmp = node->rb_left;
  do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_68(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(successor->rb_left) == sizeof(char) || sizeof(successor->rb_left) == sizeof(short) || sizeof(successor->rb_left) == sizeof(int) || sizeof(successor->rb_left) == sizeof(long)) || sizeof(successor->rb_left) == sizeof(long long))) __compiletime_assert_68(); } while (0); do { *(volatile typeof(successor->rb_left) *)&(successor->rb_left) = (tmp); } while (0); } while (0);
  rb_set_parent(tmp, successor);

  pc = node->__rb_parent_color;
  tmp = ((struct rb_node *)(pc & ~3));
  __rb_change_child(node, successor, tmp, root);

  if (child2) {
   rb_set_parent_color(child2, parent, 1);
   rebalance = ((void *)0);
  } else {
   rebalance = (((successor)->__rb_parent_color) & 1) ? parent : ((void *)0);
  }
  successor->__rb_parent_color = pc;
  tmp = successor;
 }

 augment->propagate(tmp, ((void *)0));
 return rebalance;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
rb_erase_augmented(struct rb_node *node, struct rb_root *root,
     const struct rb_augment_callbacks *augment)
{
 struct rb_node *rebalance = __rb_erase_augmented(node, root, augment);
 if (rebalance)
  __rb_erase_color(rebalance, root, augment->rotate);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
rb_erase_augmented_cached(struct rb_node *node, struct rb_root_cached *root,
     const struct rb_augment_callbacks *augment)
{
 if (root->rb_leftmost == node)
  root->rb_leftmost = rb_next(node);
 rb_erase_augmented(node, &root->rb_root, augment);
}
# 13 "lib/rbtree.c" 2
# 59 "lib/rbtree.c"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void rb_set_black(struct rb_node *rb)
{
 rb->__rb_parent_color += 1;
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) struct rb_node *rb_red_parent(struct rb_node *red)
{
 return (struct rb_node *)red->__rb_parent_color;
}






static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void
__rb_rotate_set_parents(struct rb_node *old, struct rb_node *new,
   struct rb_root *root, int color)
{
 struct rb_node *parent = ((struct rb_node *)((old)->__rb_parent_color & ~3));
 new->__rb_parent_color = old->__rb_parent_color;
 rb_set_parent_color(old, new, color);
 __rb_change_child(old, new, parent, root);
}

static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
__rb_insert(struct rb_node *node, struct rb_root *root,
     void (*augment_rotate)(struct rb_node *old, struct rb_node *new))
{
 struct rb_node *parent = rb_red_parent(node), *gparent, *tmp;

 while (true) {



  if (__builtin_expect(!!(!parent), 0)) {





   rb_set_parent_color(node, ((void *)0), 1);
   break;
  }







  if((((parent)->__rb_parent_color) & 1))
   break;

  gparent = rb_red_parent(parent);

  tmp = gparent->rb_right;
  if (parent != tmp) {
   if (tmp && (!(((tmp)->__rb_parent_color) & 1))) {
# 131 "lib/rbtree.c"
    rb_set_parent_color(tmp, gparent, 1);
    rb_set_parent_color(parent, gparent, 1);
    node = gparent;
    parent = ((struct rb_node *)((node)->__rb_parent_color & ~3));
    rb_set_parent_color(node, parent, 0);
    continue;
   }

   tmp = parent->rb_right;
   if (node == tmp) {
# 154 "lib/rbtree.c"
    tmp = node->rb_left;
    do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_69(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(parent->rb_right) == sizeof(char) || sizeof(parent->rb_right) == sizeof(short) || sizeof(parent->rb_right) == sizeof(int) || sizeof(parent->rb_right) == sizeof(long)) || sizeof(parent->rb_right) == sizeof(long long))) __compiletime_assert_69(); } while (0); do { *(volatile typeof(parent->rb_right) *)&(parent->rb_right) = (tmp); } while (0); } while (0);
    do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_70(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(node->rb_left) == sizeof(char) || sizeof(node->rb_left) == sizeof(short) || sizeof(node->rb_left) == sizeof(int) || sizeof(node->rb_left) == sizeof(long)) || sizeof(node->rb_left) == sizeof(long long))) __compiletime_assert_70(); } while (0); do { *(volatile typeof(node->rb_left) *)&(node->rb_left) = (parent); } while (0); } while (0);
    if (tmp)
     rb_set_parent_color(tmp, parent,
           1);
    rb_set_parent_color(parent, node, 0);
    augment_rotate(parent, node);
    parent = node;
    tmp = node->rb_right;
   }
# 176 "lib/rbtree.c"
   do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_71(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(gparent->rb_left) == sizeof(char) || sizeof(gparent->rb_left) == sizeof(short) || sizeof(gparent->rb_left) == sizeof(int) || sizeof(gparent->rb_left) == sizeof(long)) || sizeof(gparent->rb_left) == sizeof(long long))) __compiletime_assert_71(); } while (0); do { *(volatile typeof(gparent->rb_left) *)&(gparent->rb_left) = (tmp); } while (0); } while (0);
   do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_72(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(parent->rb_right) == sizeof(char) || sizeof(parent->rb_right) == sizeof(short) || sizeof(parent->rb_right) == sizeof(int) || sizeof(parent->rb_right) == sizeof(long)) || sizeof(parent->rb_right) == sizeof(long long))) __compiletime_assert_72(); } while (0); do { *(volatile typeof(parent->rb_right) *)&(parent->rb_right) = (gparent); } while (0); } while (0);
   if (tmp)
    rb_set_parent_color(tmp, gparent, 1);
   __rb_rotate_set_parents(gparent, parent, root, 0);
   augment_rotate(gparent, parent);
   break;
  } else {
   tmp = gparent->rb_left;
   if (tmp && (!(((tmp)->__rb_parent_color) & 1))) {

    rb_set_parent_color(tmp, gparent, 1);
    rb_set_parent_color(parent, gparent, 1);
    node = gparent;
    parent = ((struct rb_node *)((node)->__rb_parent_color & ~3));
    rb_set_parent_color(node, parent, 0);
    continue;
   }

   tmp = parent->rb_left;
   if (node == tmp) {

    tmp = node->rb_right;
    do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_73(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(parent->rb_left) == sizeof(char) || sizeof(parent->rb_left) == sizeof(short) || sizeof(parent->rb_left) == sizeof(int) || sizeof(parent->rb_left) == sizeof(long)) || sizeof(parent->rb_left) == sizeof(long long))) __compiletime_assert_73(); } while (0); do { *(volatile typeof(parent->rb_left) *)&(parent->rb_left) = (tmp); } while (0); } while (0);
    do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_74(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(node->rb_right) == sizeof(char) || sizeof(node->rb_right) == sizeof(short) || sizeof(node->rb_right) == sizeof(int) || sizeof(node->rb_right) == sizeof(long)) || sizeof(node->rb_right) == sizeof(long long))) __compiletime_assert_74(); } while (0); do { *(volatile typeof(node->rb_right) *)&(node->rb_right) = (parent); } while (0); } while (0);
    if (tmp)
     rb_set_parent_color(tmp, parent,
           1);
    rb_set_parent_color(parent, node, 0);
    augment_rotate(parent, node);
    parent = node;
    tmp = node->rb_left;
   }


   do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_75(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(gparent->rb_right) == sizeof(char) || sizeof(gparent->rb_right) == sizeof(short) || sizeof(gparent->rb_right) == sizeof(int) || sizeof(gparent->rb_right) == sizeof(long)) || sizeof(gparent->rb_right) == sizeof(long long))) __compiletime_assert_75(); } while (0); do { *(volatile typeof(gparent->rb_right) *)&(gparent->rb_right) = (tmp); } while (0); } while (0);
   do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_76(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(parent->rb_left) == sizeof(char) || sizeof(parent->rb_left) == sizeof(short) || sizeof(parent->rb_left) == sizeof(int) || sizeof(parent->rb_left) == sizeof(long)) || sizeof(parent->rb_left) == sizeof(long long))) __compiletime_assert_76(); } while (0); do { *(volatile typeof(parent->rb_left) *)&(parent->rb_left) = (gparent); } while (0); } while (0);
   if (tmp)
    rb_set_parent_color(tmp, gparent, 1);
   __rb_rotate_set_parents(gparent, parent, root, 0);
   augment_rotate(gparent, parent);
   break;
  }
 }
}





static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) __attribute__((__always_inline__)) void
____rb_erase_color(struct rb_node *parent, struct rb_root *root,
 void (*augment_rotate)(struct rb_node *old, struct rb_node *new))
{
 struct rb_node *node = ((void *)0), *sibling, *tmp1, *tmp2;

 while (true) {







  sibling = parent->rb_right;
  if (node != sibling) {
   if ((!(((sibling)->__rb_parent_color) & 1))) {
# 252 "lib/rbtree.c"
    tmp1 = sibling->rb_left;
    do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_77(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(parent->rb_right) == sizeof(char) || sizeof(parent->rb_right) == sizeof(short) || sizeof(parent->rb_right) == sizeof(int) || sizeof(parent->rb_right) == sizeof(long)) || sizeof(parent->rb_right) == sizeof(long long))) __compiletime_assert_77(); } while (0); do { *(volatile typeof(parent->rb_right) *)&(parent->rb_right) = (tmp1); } while (0); } while (0);
    do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_78(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(sibling->rb_left) == sizeof(char) || sizeof(sibling->rb_left) == sizeof(short) || sizeof(sibling->rb_left) == sizeof(int) || sizeof(sibling->rb_left) == sizeof(long)) || sizeof(sibling->rb_left) == sizeof(long long))) __compiletime_assert_78(); } while (0); do { *(volatile typeof(sibling->rb_left) *)&(sibling->rb_left) = (parent); } while (0); } while (0);
    rb_set_parent_color(tmp1, parent, 1);
    __rb_rotate_set_parents(parent, sibling, root,
       0);
    augment_rotate(parent, sibling);
    sibling = tmp1;
   }
   tmp1 = sibling->rb_right;
   if (!tmp1 || (((tmp1)->__rb_parent_color) & 1)) {
    tmp2 = sibling->rb_left;
    if (!tmp2 || (((tmp2)->__rb_parent_color) & 1)) {
# 280 "lib/rbtree.c"
     rb_set_parent_color(sibling, parent,
           0);
     if ((!(((parent)->__rb_parent_color) & 1)))
      rb_set_black(parent);
     else {
      node = parent;
      parent = ((struct rb_node *)((node)->__rb_parent_color & ~3));
      if (parent)
       continue;
     }
     break;
    }
# 319 "lib/rbtree.c"
    tmp1 = tmp2->rb_right;
    do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_79(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(sibling->rb_left) == sizeof(char) || sizeof(sibling->rb_left) == sizeof(short) || sizeof(sibling->rb_left) == sizeof(int) || sizeof(sibling->rb_left) == sizeof(long)) || sizeof(sibling->rb_left) == sizeof(long long))) __compiletime_assert_79(); } while (0); do { *(volatile typeof(sibling->rb_left) *)&(sibling->rb_left) = (tmp1); } while (0); } while (0);
    do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_80(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(tmp2->rb_right) == sizeof(char) || sizeof(tmp2->rb_right) == sizeof(short) || sizeof(tmp2->rb_right) == sizeof(int) || sizeof(tmp2->rb_right) == sizeof(long)) || sizeof(tmp2->rb_right) == sizeof(long long))) __compiletime_assert_80(); } while (0); do { *(volatile typeof(tmp2->rb_right) *)&(tmp2->rb_right) = (sibling); } while (0); } while (0);
    do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_81(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(parent->rb_right) == sizeof(char) || sizeof(parent->rb_right) == sizeof(short) || sizeof(parent->rb_right) == sizeof(int) || sizeof(parent->rb_right) == sizeof(long)) || sizeof(parent->rb_right) == sizeof(long long))) __compiletime_assert_81(); } while (0); do { *(volatile typeof(parent->rb_right) *)&(parent->rb_right) = (tmp2); } while (0); } while (0);
    if (tmp1)
     rb_set_parent_color(tmp1, sibling,
           1);
    augment_rotate(sibling, tmp2);
    tmp1 = sibling;
    sibling = tmp2;
   }
# 342 "lib/rbtree.c"
   tmp2 = sibling->rb_left;
   do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_82(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(parent->rb_right) == sizeof(char) || sizeof(parent->rb_right) == sizeof(short) || sizeof(parent->rb_right) == sizeof(int) || sizeof(parent->rb_right) == sizeof(long)) || sizeof(parent->rb_right) == sizeof(long long))) __compiletime_assert_82(); } while (0); do { *(volatile typeof(parent->rb_right) *)&(parent->rb_right) = (tmp2); } while (0); } while (0);
   do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_83(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(sibling->rb_left) == sizeof(char) || sizeof(sibling->rb_left) == sizeof(short) || sizeof(sibling->rb_left) == sizeof(int) || sizeof(sibling->rb_left) == sizeof(long)) || sizeof(sibling->rb_left) == sizeof(long long))) __compiletime_assert_83(); } while (0); do { *(volatile typeof(sibling->rb_left) *)&(sibling->rb_left) = (parent); } while (0); } while (0);
   rb_set_parent_color(tmp1, sibling, 1);
   if (tmp2)
    rb_set_parent(tmp2, parent);
   __rb_rotate_set_parents(parent, sibling, root,
      1);
   augment_rotate(parent, sibling);
   break;
  } else {
   sibling = parent->rb_left;
   if ((!(((sibling)->__rb_parent_color) & 1))) {

    tmp1 = sibling->rb_right;
    do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_84(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(parent->rb_left) == sizeof(char) || sizeof(parent->rb_left) == sizeof(short) || sizeof(parent->rb_left) == sizeof(int) || sizeof(parent->rb_left) == sizeof(long)) || sizeof(parent->rb_left) == sizeof(long long))) __compiletime_assert_84(); } while (0); do { *(volatile typeof(parent->rb_left) *)&(parent->rb_left) = (tmp1); } while (0); } while (0);
    do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_85(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(sibling->rb_right) == sizeof(char) || sizeof(sibling->rb_right) == sizeof(short) || sizeof(sibling->rb_right) == sizeof(int) || sizeof(sibling->rb_right) == sizeof(long)) || sizeof(sibling->rb_right) == sizeof(long long))) __compiletime_assert_85(); } while (0); do { *(volatile typeof(sibling->rb_right) *)&(sibling->rb_right) = (parent); } while (0); } while (0);
    rb_set_parent_color(tmp1, parent, 1);
    __rb_rotate_set_parents(parent, sibling, root,
       0);
    augment_rotate(parent, sibling);
    sibling = tmp1;
   }
   tmp1 = sibling->rb_left;
   if (!tmp1 || (((tmp1)->__rb_parent_color) & 1)) {
    tmp2 = sibling->rb_right;
    if (!tmp2 || (((tmp2)->__rb_parent_color) & 1)) {

     rb_set_parent_color(sibling, parent,
           0);
     if ((!(((parent)->__rb_parent_color) & 1)))
      rb_set_black(parent);
     else {
      node = parent;
      parent = ((struct rb_node *)((node)->__rb_parent_color & ~3));
      if (parent)
       continue;
     }
     break;
    }

    tmp1 = tmp2->rb_left;
    do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_86(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(sibling->rb_right) == sizeof(char) || sizeof(sibling->rb_right) == sizeof(short) || sizeof(sibling->rb_right) == sizeof(int) || sizeof(sibling->rb_right) == sizeof(long)) || sizeof(sibling->rb_right) == sizeof(long long))) __compiletime_assert_86(); } while (0); do { *(volatile typeof(sibling->rb_right) *)&(sibling->rb_right) = (tmp1); } while (0); } while (0);
    do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_87(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(tmp2->rb_left) == sizeof(char) || sizeof(tmp2->rb_left) == sizeof(short) || sizeof(tmp2->rb_left) == sizeof(int) || sizeof(tmp2->rb_left) == sizeof(long)) || sizeof(tmp2->rb_left) == sizeof(long long))) __compiletime_assert_87(); } while (0); do { *(volatile typeof(tmp2->rb_left) *)&(tmp2->rb_left) = (sibling); } while (0); } while (0);
    do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_88(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(parent->rb_left) == sizeof(char) || sizeof(parent->rb_left) == sizeof(short) || sizeof(parent->rb_left) == sizeof(int) || sizeof(parent->rb_left) == sizeof(long)) || sizeof(parent->rb_left) == sizeof(long long))) __compiletime_assert_88(); } while (0); do { *(volatile typeof(parent->rb_left) *)&(parent->rb_left) = (tmp2); } while (0); } while (0);
    if (tmp1)
     rb_set_parent_color(tmp1, sibling,
           1);
    augment_rotate(sibling, tmp2);
    tmp1 = sibling;
    sibling = tmp2;
   }

   tmp2 = sibling->rb_right;
   do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_89(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(parent->rb_left) == sizeof(char) || sizeof(parent->rb_left) == sizeof(short) || sizeof(parent->rb_left) == sizeof(int) || sizeof(parent->rb_left) == sizeof(long)) || sizeof(parent->rb_left) == sizeof(long long))) __compiletime_assert_89(); } while (0); do { *(volatile typeof(parent->rb_left) *)&(parent->rb_left) = (tmp2); } while (0); } while (0);
   do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_90(void) __attribute__((__error__("Unsupported access size for {READ,WRITE}_ONCE()."))); if (!((sizeof(sibling->rb_right) == sizeof(char) || sizeof(sibling->rb_right) == sizeof(short) || sizeof(sibling->rb_right) == sizeof(int) || sizeof(sibling->rb_right) == sizeof(long)) || sizeof(sibling->rb_right) == sizeof(long long))) __compiletime_assert_90(); } while (0); do { *(volatile typeof(sibling->rb_right) *)&(sibling->rb_right) = (parent); } while (0); } while (0);
   rb_set_parent_color(tmp1, sibling, 1);
   if (tmp2)
    rb_set_parent(tmp2, parent);
   __rb_rotate_set_parents(parent, sibling, root,
      1);
   augment_rotate(parent, sibling);
   break;
  }
 }
}


void __rb_erase_color(struct rb_node *parent, struct rb_root *root,
 void (*augment_rotate)(struct rb_node *old, struct rb_node *new))
{
 ____rb_erase_color(parent, root, augment_rotate);
}
extern typeof(__rb_erase_color) __rb_erase_color; static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable___rb_erase_color91 = (void *)&__rb_erase_color; asm(".section \".export_symbol\",\"a\" ; __export_symbol___rb_erase_color: ; .asciz \"\" ; .asciz \"\" ; .balign 8 ; .quad __rb_erase_color ; .previous");
# 424 "lib/rbtree.c"
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void dummy_propagate(struct rb_node *node, struct rb_node *stop) {}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void dummy_copy(struct rb_node *old, struct rb_node *new) {}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) void dummy_rotate(struct rb_node *old, struct rb_node *new) {}

static const struct rb_augment_callbacks dummy_callbacks = {
 .propagate = dummy_propagate,
 .copy = dummy_copy,
 .rotate = dummy_rotate
};

void rb_insert_color(struct rb_node *node, struct rb_root *root)
{
 __rb_insert(node, root, dummy_rotate);
}
extern typeof(rb_insert_color) rb_insert_color; static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable_rb_insert_color92 = (void *)&rb_insert_color; asm(".section \".export_symbol\",\"a\" ; __export_symbol_rb_insert_color: ; .asciz \"\" ; .asciz \"\" ; .balign 8 ; .quad rb_insert_color ; .previous");

void rb_erase(struct rb_node *node, struct rb_root *root)
{
 struct rb_node *rebalance;
 rebalance = __rb_erase_augmented(node, root, &dummy_callbacks);
 if (rebalance)
  ____rb_erase_color(rebalance, root, dummy_rotate);
}
extern typeof(rb_erase) rb_erase; static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable_rb_erase93 = (void *)&rb_erase; asm(".section \".export_symbol\",\"a\" ; __export_symbol_rb_erase: ; .asciz \"\" ; .asciz \"\" ; .balign 8 ; .quad rb_erase ; .previous");
# 456 "lib/rbtree.c"
void __rb_insert_augmented(struct rb_node *node, struct rb_root *root,
 void (*augment_rotate)(struct rb_node *old, struct rb_node *new))
{
 __rb_insert(node, root, augment_rotate);
}
extern typeof(__rb_insert_augmented) __rb_insert_augmented; static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable___rb_insert_augmented94 = (void *)&__rb_insert_augmented; asm(".section \".export_symbol\",\"a\" ; __export_symbol___rb_insert_augmented: ; .asciz \"\" ; .asciz \"\" ; .balign 8 ; .quad __rb_insert_augmented ; .previous");




struct rb_node *rb_first(const struct rb_root *root)
{
 struct rb_node *n;

 n = root->rb_node;
 if (!n)
  return ((void *)0);
 while (n->rb_left)
  n = n->rb_left;
 return n;
}
extern typeof(rb_first) rb_first; static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable_rb_first95 = (void *)&rb_first; asm(".section \".export_symbol\",\"a\" ; __export_symbol_rb_first: ; .asciz \"\" ; .asciz \"\" ; .balign 8 ; .quad rb_first ; .previous");

struct rb_node *rb_last(const struct rb_root *root)
{
 struct rb_node *n;

 n = root->rb_node;
 if (!n)
  return ((void *)0);
 while (n->rb_right)
  n = n->rb_right;
 return n;
}
extern typeof(rb_last) rb_last; static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable_rb_last96 = (void *)&rb_last; asm(".section \".export_symbol\",\"a\" ; __export_symbol_rb_last: ; .asciz \"\" ; .asciz \"\" ; .balign 8 ; .quad rb_last ; .previous");

struct rb_node *rb_next(const struct rb_node *node)
{
 struct rb_node *parent;

 if (((node)->__rb_parent_color == (unsigned long)(node)))
  return ((void *)0);





 if (node->rb_right) {
  node = node->rb_right;
  while (node->rb_left)
   node = node->rb_left;
  return (struct rb_node *)node;
 }
# 517 "lib/rbtree.c"
 while ((parent = ((struct rb_node *)((node)->__rb_parent_color & ~3))) && node == parent->rb_right)
  node = parent;

 return parent;
}
extern typeof(rb_next) rb_next; static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable_rb_next97 = (void *)&rb_next; asm(".section \".export_symbol\",\"a\" ; __export_symbol_rb_next: ; .asciz \"\" ; .asciz \"\" ; .balign 8 ; .quad rb_next ; .previous");

struct rb_node *rb_prev(const struct rb_node *node)
{
 struct rb_node *parent;

 if (((node)->__rb_parent_color == (unsigned long)(node)))
  return ((void *)0);





 if (node->rb_left) {
  node = node->rb_left;
  while (node->rb_right)
   node = node->rb_right;
  return (struct rb_node *)node;
 }





 while ((parent = ((struct rb_node *)((node)->__rb_parent_color & ~3))) && node == parent->rb_left)
  node = parent;

 return parent;
}
extern typeof(rb_prev) rb_prev; static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable_rb_prev98 = (void *)&rb_prev; asm(".section \".export_symbol\",\"a\" ; __export_symbol_rb_prev: ; .asciz \"\" ; .asciz \"\" ; .balign 8 ; .quad rb_prev ; .previous");

void rb_replace_node(struct rb_node *victim, struct rb_node *new,
       struct rb_root *root)
{
 struct rb_node *parent = ((struct rb_node *)((victim)->__rb_parent_color & ~3));


 *new = *victim;


 if (victim->rb_left)
  rb_set_parent(victim->rb_left, new);
 if (victim->rb_right)
  rb_set_parent(victim->rb_right, new);
 __rb_change_child(victim, new, parent, root);
}
extern typeof(rb_replace_node) rb_replace_node; static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable_rb_replace_node99 = (void *)&rb_replace_node; asm(".section \".export_symbol\",\"a\" ; __export_symbol_rb_replace_node: ; .asciz \"\" ; .asciz \"\" ; .balign 8 ; .quad rb_replace_node ; .previous");

void rb_replace_node_rcu(struct rb_node *victim, struct rb_node *new,
    struct rb_root *root)
{
 struct rb_node *parent = ((struct rb_node *)((victim)->__rb_parent_color & ~3));


 *new = *victim;


 if (victim->rb_left)
  rb_set_parent(victim->rb_left, new);
 if (victim->rb_right)
  rb_set_parent(victim->rb_right, new);





 __rb_change_child_rcu(victim, new, parent, root);
}
extern typeof(rb_replace_node_rcu) rb_replace_node_rcu; static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable_rb_replace_node_rcu100 = (void *)&rb_replace_node_rcu; asm(".section \".export_symbol\",\"a\" ; __export_symbol_rb_replace_node_rcu: ; .asciz \"\" ; .asciz \"\" ; .balign 8 ; .quad rb_replace_node_rcu ; .previous");

static struct rb_node *rb_left_deepest_node(const struct rb_node *node)
{
 for (;;) {
  if (node->rb_left)
   node = node->rb_left;
  else if (node->rb_right)
   node = node->rb_right;
  else
   return (struct rb_node *)node;
 }
}

struct rb_node *rb_next_postorder(const struct rb_node *node)
{
 const struct rb_node *parent;
 if (!node)
  return ((void *)0);
 parent = ((struct rb_node *)((node)->__rb_parent_color & ~3));


 if (parent && node == parent->rb_left && parent->rb_right) {


  return rb_left_deepest_node(parent->rb_right);
 } else


  return (struct rb_node *)parent;
}
extern typeof(rb_next_postorder) rb_next_postorder; static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable_rb_next_postorder101 = (void *)&rb_next_postorder; asm(".section \".export_symbol\",\"a\" ; __export_symbol_rb_next_postorder: ; .asciz \"\" ; .asciz \"\" ; .balign 8 ; .quad rb_next_postorder ; .previous");

struct rb_node *rb_first_postorder(const struct rb_root *root)
{
 if (!root->rb_node)
  return ((void *)0);

 return rb_left_deepest_node(root->rb_node);
}
extern typeof(rb_first_postorder) rb_first_postorder; static void * __attribute__((__used__)) __attribute__((__section__(".discard.addressable"))) __UNIQUE_ID___addressable_rb_first_postorder102 = (void *)&rb_first_postorder; asm(".section \".export_symbol\",\"a\" ; __export_symbol_rb_first_postorder: ; .asciz \"\" ; .asciz \"\" ; .balign 8 ; .quad rb_first_postorder ; .previous");
