# Destructor restoration loses the caller's reference value

## Violated invariant

A checked C++ destructor that restores an owned caller reference must retain
that restored value after the object's scope ends. The existing conditional
construction fixture rejects `ensures value == 41` despite a destructor
postcondition that writes the saved value back through the same pointer.

## Reproduction

With the pinned LLVM/Clang 19.1.7 exporter installed, run:

```sh
CLICK_NIGHTLY=1 cargo nextest run --profile nightly --run-ignored ignored-only \
  --test cpp_import \
  -E 'test(=conditional_construction_cleans_up_only_the_constructed_arm)'
```

The unchanged C++ source and contracts are in
`tests/fixtures/cpp-verification/conditional-construction/`. `Restore`
captures `*slot`, writes 7, and restores the captured value in its destructor.
`conditional_restore` requires its owned reference to equal 41, conditionally
constructs the guard, and either returns early or writes 9 before leaving the
guard's scope. Its postcondition requires the reference to equal 41 on every
path; the early return captures 7 before destruction.

Verification fails at the final `simp()` for `value == 41`. The diagnostic
retains ownership and view authority for `value`, the saved-field equality
to 41, and the destructor's output equality through the saved pointer, but
reports that an intervening call may have changed `value`.

The same nightly run also fails
`sibling_scopes_reuse_a_local_name_with_independent_cleanup`,
`third_sibling_scope_preserves_independent_cleanup_and_frames`, and
`scalar_int32_profile_joins_a_caught_throw_inside_conditional_cleanup` on
restoration claims. These are related reproductions; their common cause has
not yet been established. Ordinary proof tracing currently refuses typed
C++ inputs, so lowering inspection and the retained failure context are the
available evidence.

## Acceptance criteria

- The conditional-construction fixture verifies its existing result and
  reference-restoration claims without changing its C++ implementation or
  weakening its contracts.
- Its expanded certificate independently verifies, and its false result
  and restoration mutations remain rejected.
- The related cleanup regressions are checked separately, without increasing
  proof budgets or adding ambient proof-state scans.
