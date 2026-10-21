# Closing Integer postconditions after execution spends most time spelling simp premises

Soundness: performance only. The proofs verify; they take about three times
as long as they did when their postconditions were native comparisons.

Closing a function's postconditions after `execute()` should cost about what
the claims and the relevant state change need. With Integer-default
specification arithmetic, population and counter postconditions such as
`p->value == 3 - count(remaining(p))` are Integer equalities, and closing them
spends most of the run in `simp` candidate work that does not close them
before the solver does.

`mdtests/population_consumption_at_close.md` verifies in about 10.4 s in a
debug build, against about 3.2 s before the default changed (its proofs then
closed native equalities). `click profile` attributes:

```text
VERIFIER CORE      7.831s   75.2%
  5.044s     6 calls  post-execution claim tactics
  2.275s   251 calls  simp closure: premise spelling
  1.778s    15 calls  simp closure: indexed goal equality rewrite
    823ms    66 calls  simp premise surface across recorded snapshots
```

`mdtests/authority_pool_control_two_members.md` takes about 15 s, with about
4.9 s in `give_back`'s post-execution claim tactics and 3.1 s across 211
`simp closure: premise spelling` calls. Without an explicit
`open(control(p)) { have p->value == old(p->value) + 1 by auto(); }` step,
`population_consumption_at_close.md`'s `contribute_nested` alone took 12.6 s,
against 1.0 s before.

## Reproduction

From the repository root:

```sh
click profile --top 12 mdtests/population_consumption_at_close.md
click profile --top 12 mdtests/authority_pool_control_two_members.md
```

## Acceptance criteria

- Post-execution closing of an Integer postcondition does not spell or
  rewrite premises per candidate where the solver closes the goal, or bounds
  that work by the claim and the relevant state change.
- Both fixtures verify within about their pre-flip time, with a deterministic
  work regression at several sizes for the premise-spelling path
  (`docs/internals/verification-efficiency.md`).
