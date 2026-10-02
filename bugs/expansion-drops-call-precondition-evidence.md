# Expansion loses the facts a later call precondition needs

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the same claim: `click expand` output has to parse, re-verify in the retained session and through the direct targeted entry point, and contain no smart tactic at the audited site. `click audit` checks exactly this, and CLAUDE.md lists an expansion that fails or does not re-verify as a tooling defect that blocks feature work.

After one smart site is expanded, a *different* tactic of the proof (`execute()` or `step()` at a call) reports `is missing prerequisite` for the callee's precondition: bounds on the loads of a static array in five fixtures, the `strlen` existential in two. The unexpanded proof discharges the same precondition, so the expansion publishes fewer facts to the state than the smart tactic did.

The root cause has not been investigated. The fixtures below may not all share one; split this file if they do not.

## Reproduction

On `master` at `b3ab98334`, the fixture verifies (`MDTEST_FILTER=static_array_parity_fixed_multidimensional cargo test --test mdtests`) and its audit fails:

```
click audit mdtests/static_array_parity_fixed_multidimensional.md
```

fails at `mdtests/static_array_parity_fixed_multidimensional.md:36:5` (`auto`) with:

```
`call_twice.ensures_1` tactic 0: `execute()` is missing prerequisite (increment_twice precondition): (((((int32 >(load A=load(snapshot#1, pointer=&values#static0), 4294966296) is true ∧ int32 <(load A=load(snapshot#1, pointer=&values#static0), 1000) is true) ∧ int32 >(load B=load(snapshot#1, pointer=(char *)&values#static0 + 4), 4294966296) is true) ∧ int32 <(load B=load(snapshot#1, pointer=(char 
```

The gate does not audit fixtures, which is why these pass `scripts/check.sh`.

Affected fixtures (7), each failing `click audit` the same way:

- `mdtests/static_array_parity_fixed_multidimensional.md`
- `mdtests/static_array_parity_multidimensional.md`
- `mdtests/static_array_parity_scalar.md`
- `mdtests/static_local_arrays.md`
- `mdtests/static_local_array_requirement_stated_explicitly.md`
- `mdtests/cstr_dynamic_indexed_read.md`
- `mdtests/cstr_source_identity_reordered_requirement.md`

## Intended regression

Reduce `mdtests/static_array_parity_fixed_multidimensional.md` to the smallest sidecar whose audit fails this way and add it as a retained expansion-audit case, so the fixture is expanded and re-verified by the gate rather than only verified. Do not change the fixture's C or weaken its proof to make the expansion pass.

## Acceptance criteria

- `click audit` passes for every fixture listed above, with no change to their C sources or contracts.
- The reduced case is audited by `scripts/check.sh`.
- The fix is in the expander, the smart tactic's certificate, or the checker, not a per-fixture special case; `scripts/check.sh` passes.
