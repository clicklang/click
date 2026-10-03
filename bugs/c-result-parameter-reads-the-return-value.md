# `c(result)` on a parameter named `result` reads the return value

## Violated invariant

`c(name)` names the C binding `name`, never a Click built-in with the same
spelling. The language reference says bare `result` is the contract result,
while `c(result)` is a C parameter or local named `result`, and that
`c(result)` "cannot be reinterpreted as contract `result`".

For a parameter named `result`, a postcondition reads `c(result)` as the
function's return value. This proves false claims about the parameter:

```c
int32 seven(int32 result) {
    return 7;
}
```

```click
verifying "seven.c";

int32 seven(int32 result) {
    requires 0 <= c(result) and c(result) <= 100;
    ensures c(result) == 7;
}
```

This verifies, although the parameter can be any value from 0 to 100. The
same function also verifies `ensures c(result) == old(c(result));`, so the
two snapshots of one binding disagree about what it names. A failing
`ensures result == c(result) + 1` on `return result + 1;` reports the right
side evaluated to `((result + 1) + 1)`: `c(result)` became the return value.

A C local named `result` is not affected: in a script, `have c(result) == x`
before the local's assignment is refused because the local has no value yet,
so the local reading is used there.

The cause is that the contract result and C bindings share one namespace.
Bare `result` parses as the C fragment `Variable("result")`, and
`ContractExpression::CBinding` lowers through the same
`lower_c_fragment_to_spec(&CExpression::Variable(name))`
(`src/surface/lowering/annotations.rs`). The postcondition's value
environment binds the contract result under the plain key `result`
(`context.values.insert("result", ...)` in the same file), replacing the
parameter's entry, and a fixed-state `have` installs the contract result as a
C local named `result` (`with_local("result", ...)` in
`src/surface/proof/fixed_state_proofs/have_proofs.rs`). Other code compares
names against `"result"` directly, so the fix is to give the contract result
a binding no C identifier can spell, not to patch one lookup.

## Intended regression

An mdtest with `seven` above whose `ensures c(result) == 7;` must fail with
an unclosed goal, beside a passing `ensures c(result) == old(c(result));` and
a passing `ensures result == 7;`. Add the same pair for a parameter named
`result` that the function reads (`return result + 1;` with
`ensures result == c(result) + 1;` passing).

## Acceptance criteria

- In every contract position (requires, ensures, exceptional ensures, loop
  invariants, `at(...)` snapshots), `c(result)` names the C parameter or
  local, and bare `result` names the contract result.
- The regression's false claim is refused and its true claims verify.
- Expansion, which prints `c(result)` for an overlapping C binding, still
  produces source that re-verifies with the same meaning.
- `scripts/check.sh` passes.
