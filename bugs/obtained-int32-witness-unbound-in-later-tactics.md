# An `obtain`ed int32 witness is unbound in a later `have`, `instantiate`, or `contradiction`

## Violated invariant

`obtain (k: int32) { k > x }` opens an existential precondition and names
its witness `k` for the rest of the scoped proof. Existing fixtures use an
obtained algebraic binder in later tactics: `obtain (previous: Nat) { ... }`
followed by `apply(nat_reflexive(previous))`, and `obtain (rest: Path) { ...
}` followed by `have walk(..., Path::Left(rest)) == to by { ... }`
(`mdtests/algebraic_existential_witness.md`, `mdtests/branching_graph_dfs.md`).
An obtained `int32` binder in a pure theorem is not in scope for the same
tactics: `have k > x`, `instantiate(forall ..., k) using { k > x; }`, and
`contradiction(k < x)` are each refused with `unbound variable k`. Only
`witness { ... }` sees it. The lowering of a later tactic's proposition
(`src/surface/proof/pure_theorems.rs` and the `have`/`instantiate` premise
lowering) does not consult the scope the `obtain` extended for machine-integer
binders.

## Reproduction

```click
theorem ob(x: int32) {
    requires exists (k: int32) { k > x };
    requires forall (j: int32) { j > x implies j > 1000 };
    ensures x < 1000 by {
        obtain (k: int32) { k > x }
        instantiate(forall (j: int32) { j > x implies j > 1000 }, k) using { k > x; }
        simp();
    }
}
```

Observed on 2026-10-07:

```text
proof error:
  could not lower `instantiate using` premise
  pure theorem `ob.ensures_0`
  the kernel lowering produced no path
  every evaluation path ended in a runtime error
  unbound variable `k`
```

`have k > x by { assumption(); }` after the `obtain` fails the same way, and
so does `contradiction(m < k)` after two obtains.

## Intended regression

The theorem above as a positive mdtest, and a two-witness variant with
`obtain (k) { k > x }`, `obtain (m) { m < x }`, `have k > x`, `have m < x`,
and `contradiction(m < k)` closing `0 == 1`; today the `have` fails to lower.

## Acceptance criteria

- A binder introduced by `obtain` in a pure theorem is in scope for every
  later tactic of the same scoped proof, for machine-integer, `Integer`, and
  algebraic binders alike.
- A proposition naming a variable that is genuinely unbound still reports
  `unbound variable`.
- `scripts/check.sh` passes.
