# The refusal of `old(c.model)` in a loop clause suggests a binding that is rejected

## Violated invariant

A diagnostic that proposes a spelling proposes one the verifier accepts. When a loop invariant reads `old(c.model)` and the loop's entry state holds no instance named `c`, the refusal says:

```
`c.model` reads a field of `c`, which is not held here; when `unfold(c)` consumed it, name the field's folded value where the instance is unfolded with `let { model: name } = unfold(c);` and write `name` instead
```

Both halves of the advice are wrong for a modelled instance:

- `let { model: name } = unfold(c);` is rejected for an algebraic field. On the rbtree resource it reads: "field `model` of `rb_at` is not C-typed; an unfold pattern binds only C scalar and pointer fields, so read an algebraic field's payload with a proof `match` on `t.model` before the unfold".
- `c` need not have been unfolded at all. In the reduction it was consumed by a `fold` that made it a child of another instance, so there is no `unfold(c)` to put a binding on.

The refusal itself is a separate question, reported with the reduction below and not filed here: decision D5 in `issues/rbtree-example.md` says `old(name.field)` in a loop clause keeps its meaning, the function-entry instance of the function-level binder, yet it is read through the instance of that name the loop's entry state holds.

## Reproduction

`mdtests/loop_invariant_old_model_of_an_instance_folded_into_a_parent.md` reaches the message. Following its advice in any proof whose resource has `field model: <spec enum>` produces the second refusal quoted above.

## Intended regression

Pin the diagnostic on the fixture above with an `expect fail` substring that names a remedy the fixture can apply, and add the remedy as a neighbouring positive.

## Acceptance criteria

- The message distinguishes an instance consumed by `unfold` from one consumed as a child of a `fold`, and from one never held.
- For an algebraic field it does not suggest an unfold-pattern binding; it suggests a spelling that verifies, or says that none exists.
- `scripts/check.sh` passes.
