/* Click's declaration-only x86-64 Linux user-space projection of the
 * <stdatomic.h> subset selected for one-shot release/acquire publication.
 * These declarations carry no executable or external-contract semantics.
 * `atomic_int` has the x86-64 size and alignment of `int`; its bytes are
 * opaque, so a plain read or write of the object, which C11 would perform
 * with sequentially consistent ordering, is not in the subset. The generic
 * operations are projected for `atomic_int` only, with the order passed as
 * the `int` value of its `memory_order` constant.
 */
#pragma once
typedef union __click_atomic_int {
    char __size[4];
    int __align;
} atomic_int;
enum memory_order {
    memory_order_relaxed,
    memory_order_consume,
    memory_order_acquire,
    memory_order_release,
    memory_order_acq_rel,
    memory_order_seq_cst
};
typedef enum memory_order memory_order;

void atomic_init(atomic_int *object, int value);
void atomic_store_explicit(atomic_int *object, int desired, int order);
int atomic_load_explicit(atomic_int *object, int order);
