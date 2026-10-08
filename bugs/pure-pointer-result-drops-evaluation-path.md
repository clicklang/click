# Pointer-returning pure functions silently lose their evaluation path

## Violated invariant

A well-typed pure function application must lower to its declared value type,
or fail with an explicit supported-type diagnostic. A pointer result must not
silently disappear because the scalar evaluator only constructs bitvectors.
The current declaration is accepted, but its application fails with the
misleading internal diagnostic `the kernel lowering produced 0 paths, not one`.

## Reproduction

Save the following as `pointer-result.click` and run
`target/debug/click verify pointer-result.click`:

```click
function identity(p: int32*) -> int32* { p }
function holds(p: int32*) -> int32 { 1 }
theorem use_identity(p: int32*) {
    ensures holds(identity(p)) == 1 by {
        unfold(holds(identity(p))); normalize();
    }
}
```

Reproduced on `446be6da0`. Verification exits 1 before executing the proof:

```text
`use_identity.ensures_0` failed
could not lower conclusion
pure theorem `use_identity`
the kernel lowering produced 0 paths, not one
```

The same failure occurs when the pointer-returning function matches an enum
with `Empty => 0` and `Node(p) => p`. It is not specific to null typing,
recursion, C layout import, or the rbtree model.

## Cause and impact

`evaluate_spec_pure_function_application_paths_in` in `src/kernel/spec.rs`
constructs every C-valued application through `c_value_from_bitvector_term`.
That helper has no pointer case. Its `None` result takes `continue`, discarding
the otherwise valid argument path without a diagnostic.

The rbtree deeper-successor proof needs the parent of the minimum node as a
pointer-valued model selector. This defect blocks the direct expression of
plugging its replacement child into the accumulated descent context. The
unverified prototype was removed; the verified immediate-successor sidecars
remain intact. No C source was changed.

## Intended regression and acceptance

- Turn the reproduction into a passing mdtest, including a pointer equality
  after unfolding `identity`, rather than only an ignored argument.
- Cover an enum selector with null and non-null arms and a recursive selector
  used as another pure function's pointer argument.
- Preserve pointer type and provenance in the result. Do not represent the
  pointer as an integer address or grant memory ownership from the result.
- Add negatives for unequal pointers and attempts to read through a result
  without ownership. Exercise substitution under binders and distinct calls
  so no result can alias merely because a fresh name was reused.
- Ordinary verification and expansion/audit must agree. Keep evaluation and
  substitution proportional to the explicit expression, with deterministic
  scaling coverage for any new representation or walker.
- Unsupported result types must produce a local diagnostic, never silently
  discard an evaluation path.
