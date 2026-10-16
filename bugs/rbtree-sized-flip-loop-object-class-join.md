# Existing sized color-flip proof fails the pointer object-class loop join

## Reproduction

At upstream `296760674`, build the CLI and run:

```sh
click verify --trace-proof __rb_insert examples/rbtree-augmented/rbtree_size_insert_context_color_flip.click
```

The unchanged checked sidecar fails at `close_invariants by simp` (line 362):

```text
loop state join changes pointer object classes; the body path does not reach the loop-head state
```

This reproduces on an isolated worktree at unmodified upstream, without PR
#1256's pointer-call congruence. The same proof fails identically with that
feature. The sidecar was last changed by `b3594588a` (PR #1240), which had
verified all three selected claims before publication. This is an integration
regression in an existing example; the exact class mismatch remains unclassified.
The current loop error discards the local name and both compared object classes.
A simple aligned-pointer masking loop passes, so that alone is not the reduction.

## Acceptance

Identify the exact loop-head/back-edge local and classes, reduce the failure,
and restore the existing sized color-flip proof. Preserve strict-aliasing and
object-class negative controls; do not drop the class check or change the pinned
Linux C to make the proof pass. Retain a targeted regression for the cause and
remove this report when the fix and regression land.

## Diagnosis from the exact join diagnostic

The failing local is `node`: its loop-head object class is `struct rb_node`,
but its back-edge class is unknown (no retained object class). The color-flip
path assigns `node = gparent`; `gparent` is recovered by `rb_red_parent` from
the packed integer parent word. `cast_c_value_to_type` reconstructs a bare
`Pointer` through `cast_tagged_address_to_pointer` and then creates a new
`CValue::typed_pointer`, which carries no original object class. The loop check
correctly refuses to silently reinstate information that is absent at the edge.
Do not infer the original object's class from the destination cast type.

The following smaller self-link loop reproduces the same class loss for `p`.
Its pointer value is proved unchanged; repeated iterations still lose the
annotation. Changing its decrement to `more = 0` passes because the loop exits.

```c filename=packed.c
struct node { uint64 parent_word; };
void follow(struct node* p, int32 more) {
    while (more) { p = (struct node*)p->parent_word; more = more - 1; }
}
```
```click
verifying "packed.c";
resource self_link(p: struct node*) {
    field word: uint64;
    owns p->parent_word;
    fact p->parent_word == word;
    fact word == address(p);
}
void follow(struct node* p, int32 more) {
    owns held: self_link(p);
    requires 0 <= more;
    ensures 1 == 1;
} by {
    loop {
        owns held: self_link(old(p));
        decreases more;
        invariant p == old(p);
        invariant 0 <= more;
        initialize by simp;
        preserve by {
            let { word: saved_word } = unfold(held);
            have p->parent_word == address(p) by { assumption(); }
            step(); step();
            let held = fold(self_link(old(p)), { word: saved_word });
            close_invariants by simp;
        }
    }
    execute();
}
```
```expect
pass
```

## Additional affected audit regression

The unchanged named nightly regression also fails before its expansion/audit
checks:

```sh
cargo nextest run --bin click --profile nightly --run-ignored only \
  -E 'test(=audit::tests::loop_expansion_preserves_match_pointer_theorem_arguments_and_audits_every_site)'
```

Its original `rb_root_of.contract` rejects the loop preservation join with
`parent` carrying `struct rb_node` at the head and no retained object class on
the back edge. This regression uses `mdtests/rb_ascending_walk_to_root.md` and
adds pointer-theorem calls in a matched context frame. Include it when checking
the eventual class-preservation fix; it must verify before expansion can run.
