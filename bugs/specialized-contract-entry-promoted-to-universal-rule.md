# Specialized contract executions can become unrestricted function rules

## Violated invariant

A reusable `CVerifiedFunctionRule` must establish its contract for every input
satisfying its preconditions. A checked execution at one particular argument,
or with two otherwise independent arguments identified, is insufficient.

The public certification and rule-packaging APIs accept such specialization.
A function that returns zero with no preconditions can acquire the false
postcondition `x == 0` after checking only the call with `x = 0`. Using the same
symbolic value for `x` and `y` similarly certifies `x == y` without an alias
precondition.

`c_verified_function_contract_claims` produces claims from the complete frontier
of the supplied execution. `c_verified_function_rule` checks completeness and
exact function identity, but the packaged claims do not retain a checked
justification that the entry covered all permitted inputs. The resulting rule
has neither the specialized arguments nor guards restricting its application.

The reproduction uses kernel APIs and the existing test helper; a Surface
source program exposing this path has not been established. This blocks adding
reusable construction-result guarantees: checking a particular destination
cannot justify a summary for arbitrary caller destinations.

## Reproduction

Append these tests to `src/kernel/tests/contract_execution_tests.rs`, where
`certify_contract_with_kernel_artifacts` is already in scope. They use the
kernel's own checked artifacts, not forged private claim or rule values.

```rust
#[test]
fn a_single_concrete_call_cannot_certify_a_universal_function_rule() {
    let function = c_function(
        CType::Int32,
        "specialized_entry_probe",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        vec![],
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("x")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_int32_literal(0)),
        }],
        vec![],
        vec![
            CFunctionContractClaim::body_safety(),
            CFunctionContractClaim::ensure_proposition(0, 0),
        ],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        CState::new(),
        function.clone(),
        vec![c_int32_literal(0)],
        vec![],
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    let Some(claims) = c_verified_function_contract_claims(&function, &execution) else {
        return;
    };
    assert!(
        c_verified_function_rule(function, &claims).is_none(),
        "one successful input must not certify an unrestricted rule"
    );
}

#[test]
fn aliased_symbolic_arguments_cannot_certify_an_unrestricted_function_rule() {
    let function = c_function(
        CType::Int32,
        "aliased_entry_probe",
        vec![
            c_parameter("x", CType::Int32),
            c_parameter("y", CType::Int32),
        ],
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        vec![],
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("x")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_variable("y")),
        }],
        vec![],
        vec![
            CFunctionContractClaim::body_safety(),
            CFunctionContractClaim::ensure_proposition(0, 0),
        ],
        true,
    );
    let value = CExpression::Value(int32(Bitvector32Term::Variable(Variable(872_001))));
    let execution = certify_contract_with_kernel_artifacts(
        CState::new(),
        function.clone(),
        vec![value.clone(), value],
        vec![],
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    let Some(claims) = c_verified_function_contract_claims(&function, &execution) else {
        return;
    };
    assert!(
        c_verified_function_rule(function, &claims).is_none(),
        "a proof with x and y identified must not certify independent arguments"
    );
}
```

Run:

```sh
cargo nextest run --lib --no-fail-fast -E \
  'test(a_single_concrete_call_cannot_certify_a_universal_function_rule) | test(aliased_symbolic_arguments_cannot_certify_an_unrestricted_function_rule)'
```

Confirmed on clean upstream commit `309af5175`, with only these two tests
added in a separate worktree. Both fail their final rule-rejection assertion
(0 passed, 2 failed; about 0.02 seconds test execution). The same concrete-input
failure was first reproduced while implementing aggregate initialization;
none of those implementation changes is required to trigger either failure.

The intended result is rejection at certification or rule promotion. Particular
executions may remain valid; they must not establish unrestricted rules.

## Acceptance criteria

- Reject both regressions unless the declared preconditions entail the supplied
  specialization. Checking that arguments are symbolic is insufficient when
  two arguments share a symbol.
- Check generic-entry provenance in the kernel, or preserve checked restrictions
  on the rule and enforce them at every application. A frontend-provided trust
  flag is insufficient.
- Cover pointer alias restrictions and extra input-memory knowledge as well as
  scalar argument specialization. Any new construction destination participates
  in this same generality check.
- Preserve useful proofs about individual calls, valid generic function rules,
  and agreement between ordinary, expanded, and retained verification.
- Keep entry validation proportional to the function's actual input schema and
  proof evidence; do not introduce per-call scans of unrelated state.

The recommended design is checked generic-entry evidence for unrestricted
rules, while keeping particular-call proofs separate. Supporting reusable
specialized rules would instead require explicit guards and checked transport
of those guards through every application path.
