# A postcondition about a parameter named `result` cannot be certified

## Violated invariant

`c(name)` names the C binding `name`, and a true claim about existing C that
Click's semantics cover must be provable. A C function may name a parameter
`result`; the language reference says `c(result)` reads that parameter while
bare `result` is the contract result.

The kernel stores the return value in the exit state as a local named
`result` (`set_typed("result", ...)` in
`src/kernel/api/contract_certification/contract_claims.rs` and
`src/kernel/functions.rs`), replacing the parameter's binding. Surface
lowering does the same for the fixed-state proof context
(`context.values.insert("result", ...)` in
`src/surface/lowering/annotations.rs`, `with_local("result", ...)` in
`src/surface/proof/fixed_state_proofs/have_proofs.rs`), and other code
compares names against `"result"` directly. The contract result and the C
binding share one name.

`c(result)` used to be read as the return value wherever the contract result
was in scope, which proved false claims about the parameter. That is now
refused (`mdtests/c_result_parameter_is_refused_where_the_contract_result_is_in_scope.md`).
What remains is completeness: a true postcondition that reads the parameter
through a snapshot still fails contract certification.

```c
int32 bump(int32 result) {
    return result + 1;
}
```

```click
verifying "bump.c";

int32 bump(int32 result) {
    requires 0 <= c(result) and c(result) <= 100;
    ensures result == old(c(result)) + 1;
}
```

The claim's proof closes, but contract certification reports
`exact symbolic execution did not establish every contract claim`. The same
happens for `at(function.entry, c(result))`. The failure predates the
refusal above.

## Intended regression

An mdtest with `bump` above whose `ensures result == old(c(result)) + 1;`
verifies, beside the existing refusal fixture, a failing
`ensures result == old(c(result)) + 2;`, and a passing claim through
`at(function.entry, c(result))`.

## Acceptance criteria

- The contract result has an internal binding no C identifier can spell, as
  the exceptional value already does (`C_EXCEPTIONAL_RESULT_NAME`), in the
  kernel's exit state and in surface lowering; bare `result` names it.
- `c(result)` names the C parameter or local in every contract position,
  including postconditions, so the refusal can be removed.
- The regression's true claims verify and certify, and its false claim fails.
- Expansion, which prints `c(result)` for an overlapping C binding, still
  produces source that re-verifies with the same meaning.
- `scripts/check.sh` passes.
