# `auto` expansion re-verifies against a callee with no verified clause

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the same claim: `click expand` output has to parse, re-verify in the retained session and through the direct targeted entry point, and contain no smart tactic at the audited site. `click audit` checks exactly this, and CLAUDE.md lists an expansion that fails or does not re-verify as a tooling defect that blocks feature work.

Every failure is at an `auto` site in a sidecar where one function's claim is proved by `auto` and another function calls it or is external. After the site is rewritten, re-verification reports that a verified function has no verified `ensures` (or `requires`) clause of the index the caller's proof uses. The original sidecar verifies, so the rewrite or the targeted re-verification drops or renumbers a clause the unexpanded run had.

The root cause has not been investigated. The fixtures below may not all share one; split this file if they do not.

## Reproduction

On `master` at `b3ab98334`, the fixture verifies (`MDTEST_FILTER=call_existential_direct_have cargo test --test mdtests`) and its audit fails:

```
click audit mdtests/call_existential_direct_have.md
```

fails at `mdtests/call_existential_direct_have.md:24:5` (`auto`) with:

```
verified function `child` has no verified `ensures` clause 0
```

The gate does not audit fixtures, which is why these pass `scripts/check.sh`.

Affected fixtures (17), each failing `click audit` the same way:

- `mdtests/call_existential_direct_have.md`
- `mdtests/call_existential_evaluated_load_guard.md`
- `mdtests/call_precondition_disjunction_is_an_obligation.md`
- `mdtests/call_precondition_disjunction_stated_explicitly.md`
- `mdtests/conditional_call_existential_historical_read.md`
- `mdtests/conditional_call_indexed_result_fact.md`
- `mdtests/const_pointer_return_external.md`
- `mdtests/exists_viewable_range.md`
- `mdtests/external_allocator_contract.md`
- `mdtests/external_function_contract_call.md`
- `mdtests/external_function_contract_memory.md`
- `mdtests/external_pointer_array_allocator_contract.md`
- `mdtests/external_struct_allocator_contract.md`
- `mdtests/forall_viewable_range.md`
- `mdtests/graph_view_survives_marked_summary_call.md`
- `mdtests/private_state_narrowing_call.md`
- `mdtests/viewable_range_requirement_stated_explicitly.md`

## Intended regression

Reduce `mdtests/call_existential_direct_have.md` to the smallest sidecar whose audit fails this way and add it as a retained expansion-audit case, so the fixture is expanded and re-verified by the gate rather than only verified. Do not change the fixture's C or weaken its proof to make the expansion pass.

## Acceptance criteria

- `click audit` passes for every fixture listed above, with no change to their C sources or contracts.
- The reduced case is audited by `scripts/check.sh`.
- The fix is in the expander, the smart tactic's certificate, or the checker, not a per-fixture special case; `scripts/check.sh` passes.
