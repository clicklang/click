# Loop `break` exits that made different calls do not join

## Violated invariant

A loop has one successor, and exits that reach the same C state join into it. `join_loop_exits` in `src/kernel/loops.rs` abstracts what the exits disagree about (binder models, locals, cells written differently) and requires the rest to be the same state. Two exits that hold the same cells and own the same resources are refused when one of them called a function that declares a local and the other did not:

```
loop exits reach different states, so they have no common successor: memory
```

The exits differ in three components, all of them the path's record of automatic storage rather than anything the C can observe after the loop:

1. `CMemory::forgotten.ended_local_blocks`: the calling path holds a tombstone for the callee's ended local (`local:lifetime:0:<name>`).
2. `CMemory::forgotten.forgotten_from`: the calling path's memory carries the forget mark that retiring that block's cell left.
3. `CState::next_local_lifetime`: the calling path took an identity from the counter; the other path did not. The locals environment differs with it.

The message names only "memory", and says neither which exits differ nor in what.

This blocks the rbtree insert proof. With all 99 `break` paths of `__rb_insert`'s loop written, the loop rule is refused this way: the rotation exits call `__rb_rotate_set_parents`, which declares `parent`, and the early exits do not. Measured on the insert frontier: the exits' blocks, heap, union cells, cells and resources agree, and `forgotten` is the reported `memory` difference (no tombstone and no mark at an early exit; `local:lifetime:0:parent` and a mark at a rotation exit). With `forgotten` set aside in an experiment the refusal becomes `the symbolic state`: the counter is 0 at the early exit and 1 at the rotation exit, and the locals environments differ. Whether anything else differs behind those was not measured.

The earlier form of this bug (exits equal up to the cell cache's layout, a view held twice, fold order) is fixed: `mdtests/loop_break_exit_join_compares_cells_not_their_cache.md`, `loop_break_exit_join_refolded_and_untouched_binder.md`, `loop_break_exit_join_ignores_fold_order.md`.

## Reproduction

`mdtests/loop_break_exit_after_a_call_with_a_local_does_not_join.md` is the reduction and pins the refusal. Replacing the call with the store it performs verifies.

## What a fix has to decide

These are not representations of one state, so each needs its own argument; none is made here.

- **Tombstones.** The interface join (`with_interface_memory_havoc_preserving_loans`) already takes the union of the siblings' ended blocks. A tombstone for a block a path never created forbids accesses that path could not make, and it disables the "this loaded pointer predates the block" inference in `loaded_pointer_predates_block`, so the union is the conservative direction. The block's identity must not be reissued after the join, which is what (3) guards.
- **The lifetime counter.** It is a monotonic identity source; the maximum over the exits is fresh on every path.
- **The forget mark.** It is a snapshot identity: a marked memory is not known to be the memory it forgot from, so a load from it at a cell it does not hold must not be named as a load from an unmarked snapshot with the same cells. A successor that keeps the cells every exit agrees on has to carry an identity no exit's memory has, so that nothing any path established about its own snapshot's unknown cells transfers.

## Intended regression

Flip `mdtests/loop_break_exit_after_a_call_with_a_local_does_not_join.md` to `expect pass`. Negatives: two exits whose callee locals differ and where a stale pointer to the ended local is read after the loop; an exit that leaves a heap allocation live that the other freed (`heap allocation lifetimes`, refused today); a load after the loop of a cell neither exit holds, which must not be equated with either exit's earlier load of it.

## Acceptance criteria

- The reduction verifies, and `examples/rbtree-insert/rbtree_insert.frontier` gets past the loop rule on the unchanged C.
- Each of the three components is joined by a stated rule with its soundness argument in the code, and the negatives above are refused.
- The refusal that remains for a real difference names the exit and the component.
- `scripts/check.sh` passes.
