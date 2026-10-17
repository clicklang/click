# Imported contracts drop typed-pointer return postconditions

Soundness: not soundness. A checked imported helper promises a typed pointer
fact on its nonnull return. The caller's symbolic return lacks that checked
type, so instantiating the postcondition drops it and a valid caller proof is
rejected. This reproduction demonstrates loss of a guarantee, not acceptance
of a false C claim.

The companion `library.click` verifies. Its `get` contract says
`result != 0 implies node_type(result) == 1`; the typed pure helper's parameter
requires an original `struct node` object or null. `caller.click` imports that
contract and fails to lower the same helper call under `q != 0`.

```console
click verify bugs/imported-contract-drops-typed-pointer-return-postcondition/library.click
click verify --trace-proof caller bugs/imported-contract-drops-typed-pointer-return-postcondition/caller.click
```

The call trace exports only its resource composition, losing the typed return
postcondition. Rbtree's `rbtree_erase_leaf.click` exposes the same defect for
`ctx_node_is(remaining.model, result)` after `__rb_erase_augmented`.

Acceptance: retain this declaration-backed guarantee for opaque/imported and
forward calls. Do not infer an original class from a bare C return declaration,
from an unrelated guard, or from a function's own unproved postcondition.
Cover unconditional and nonnull-guarded typed returns, guard separation, and a
bad actual return that must still fail the callee's proof.
