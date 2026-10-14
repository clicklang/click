# Pointer disequality is not available at its normalized offset goal

Soundness: sound. A valid consequence is refused; this reproduction does not
establish acceptance of an invalid claim.

Checked pointer facts must remain usable when C comparison lowering expresses
a same-base pointer comparison as a byte-offset comparison. The graph handles
positive offset equalities, but its condition-congruence lookup gives
`PointerEq` and `OffsetEq` different predicate kinds. A negative offset query
can be rejected by `may_know_condition` before consulting the established
pointer disequality and pointer aliases.

Reproduce with `click verify --trace-proof pointer_disequality example.click`:

```click
spec enum Model { Empty, Node(int32*) }
function model_pointer(model: Model) -> int32* {
    match model { Model::Empty => 0, Model::Node(p) => p, }
}
theorem pointer_disequality(model: Model, p: int32*, other: int32*) {
    requires model_pointer(model) == p;
    requires model_pointer(model) != other;
    ensures p != other by {
        have model_pointer(model) == p by assumption();
        have model_pointer(model) != other by assumption();
        assumption();
    }
}
```

Both `have` steps succeed. The rejected goal is displayed as
`int32(p)*4 bytes = int32(other)*4 bytes is false`. The legend identifies the
pure pointer as `model_pointer(model:Model) + 0 bytes`; its equality with `p`
and inequality with `other` are checked facts. No further premise is needed.

The rbtree metadata bridge fails the same way: it has
`sized_identity(left_model) != p` and
`sized_identity(left_model) == p->rb_left`, but cannot close `p->rb_left != p`.

Acceptance: connect pointer disequalities to equivalent common-base offset
comparisons through the shared indexed mechanism. Cover both admission orders,
branch scope, and withdrawn evidence. Unequal allocation bases alone must not
imply unequal offsets. Avoid scans of unrelated facts or address pairs; include
scaling regressions and advance the unchanged rbtree bridge past this goal.
