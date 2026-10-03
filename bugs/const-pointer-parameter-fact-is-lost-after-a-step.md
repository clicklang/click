# A fact about a `const` pointer parameter is lost after a C step

## Violated invariant

A fact about a parameter's value holds for the rest of the path, and a proposition that names the parameter means that value whatever qualifiers its type carries. Qualifiers are C typing, not part of the value: `const` decides which writes are allowed, not which pointer it is.

With `const struct node* p`, a fact the proof has about `p` stops matching `p` once a C statement has run. `mdtests/const_pointer_parameter_fact_is_lost_after_a_step.md` is the reduction: unfolding an instance at `p` publishes `same(p, p) == 1`; `assumption` finds it before the first `step()` and not after. Dropping `const` makes the fixture verify.

The likely cause, read from the code and not confirmed: a pointer's pointee constness is part of the `CPointerValue` a pure-function argument carries, and so of the fact's identity (`src/kernel/proof/fact_keys.rs` keys on it). The resource body's fact is built from the instance argument, which carries one constness. After a step, the local `p` is read back with the parameter's declared constness, so the two spellings of the same pointer are different terms.

This blocks the unchanged `const struct rb_node *node` signature of Linux `rb_next` (chunk 8). With the importer's const-dropping cast rule applied, `mdtests/rb_next.md` with the real signature fails at its first such `have`, `rb_parent_is(entry_right, node) == 1` by `assumption()`, after the two steps that test `RB_EMPTY_NODE`.

## Intended regression

Flip `mdtests/const_pointer_parameter_fact_is_lost_after_a_step.md` to `expect pass`. Add the same shape with a `const` pointer local assigned from a non-const one, and a negative showing that a write through the `const` parameter is still refused.

## Acceptance criteria

- A fact about a pointer value is found under every qualified spelling of that value, before and after C steps.
- Writes through a `const` view are still refused (`mdtests/const_pointer_cast_write_rejected.md`).
- With the const-dropping cast rule in place, `mdtests/rb_next.md` verifies with `const struct rb_node *node`.
- `scripts/check.sh` passes.
