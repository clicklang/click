# rbtree-erase `flips_red_all` is refused after its loop

Soundness: not soundness. A previously verifying proof is refused; nothing
false is accepted.

`examples/rbtree/rbtree-erase/rbtree_erase_color_flips_red_all.click` verified on
master at 6bd0854ca (2026-10-17). The C source and the sidecar are unchanged
since, so the change is in the verifier.

Two refusals introduced by #1366 are fixed (typed calls in a loop invariant
and in a `match ... ensuring` fact on reassigned pointers). Three more stand
in the loop's `preserve` proof, in this order.

## 1. Stale rewrites (proof text)

```sh
cargo build --release --bin click
target/release/click verify examples/rbtree/rbtree-erase/rbtree_erase_color_flips_red_all.click
```

```text
`rewrite` equality does not occur in the current goal
tactic@1835:91:
  rewrite(iid == sibling);
goal: tmp1 == sid
```

The verifier now resolves `iid->rb_left` to `tmp1` itself, so several
`rewrite`s have nothing to rewrite. Lines 1835, 1940 and 2015 have the form
`have A->f == Y by { rewrite(A == B); rewrite(Y == T); normalize() using {
B->f == T; }; }`, which becomes `have A->f == Y by { normalize() using { T ==
Y; }; }`. At line 2177 the single `rewrite(sid == parent->rb_left);` can be
dropped. These are proof updates, not defects.

## 2. One stored pointer read with two designations (verifier defect)

After the line-1835 update, line 1854 is refused:

```text
`assumption` requires the current goal as an available semantic fact
tactic@1854:108:
  assumption();
goal: at(<state A>, tmp1[4]) == at(<state A>, tmp1[4])
```

The source is `have sid->rb_left == at(inner_inputs, sid->rb_left) by
assumption();`, and the same `have` succeeds at line 1672. The goal is a
`PointerValueEqual` whose two sides have the same address (one load variable)
but different designations: the current read's designation is named by a later
snapshot (where `resource_tracker::last_same_point` stops at a store it cannot
separate without facts), while the `inner_inputs` read's is named by the loop
havoc snapshot. The load-variable naming crossed that store using the path's
facts, so one stored value carries two designations. The goal display prints
only the address, so both sides look identical.

The read is `canonicalized_pointer_value_from_int_cell` in
`src/kernel/eval/memory_loads.rs`: it already takes the value's block from the
variable's defining read (`registered_load_term_for_variable`) but names the
designation by the current snapshot. Naming the designation by the same
defining read, when no stored complete value is found, makes line 1854 pass.
That change lacks a reduced regression: straightforward reductions (a marked
state, a store, then the same `have`, inside and outside loops and joins) pass
on master.

## 3. Folded child pointer has no object class (needs a decision)

With 1 and 2 applied, line 2187 is refused:

```text
fold field `model`
algebraic initializer must denote one symbolic value
tactic@2187:
  let far_link = fold(rb_saved_link(&sid->rb_left), { model: RbSavedLink::Link(parent->rb_left->rb_left) });
```

The initializer lowers to no path: since #1366, `RbSavedLink::Link` needs
evidence that its `struct rb_node*` field has that class or is null, and
`sid->rb_left` (equal to `parent->rb_left->rb_left`) has none. The proof holds
the child as a folded `rb_at(sid->rb_left)` instance. Every `rb_at(p)` arm makes
`p` null or a typed model identity, but nothing derives that without matching
the child. The mirrored site is line 3649.

Two responses, to be decided by the maintainer: a verifier rule that a held
resource whose every arm types its pointer parameter (or makes it null)
supplies that class, or proof changes that match the child's model before
each saved-link fold.

`rbtree-erase` is a nightly example, so the gate does not run it.

## Acceptance criteria

- The command above verifies again, with work close to its earlier 28.8
  million units.
- A reduced gate regression covers the designation rule of item 2, and one
  covers whichever response item 3 takes.
