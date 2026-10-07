# A finite universal with an empty binder range discharges leaves that do not mention the binder

## Violated invariant

`forall (k: int32) { body }` is true only when `body` holds at every `k`. A
body that is a conjunction of guarded leaves is vacuous outside the constant
hull of the leaves' guards *only for the leaves that mention `k`*; a leaf
whose guard does not mention `k` (`x > 0 implies x == 7`) is the same
proposition at every `k` and is not made true by an empty binder range.

`finite_forall_ranges_allowing_empty`
(`src/kernel/reasoning/order_reasoning.rs:206-249`) builds the enumeration
hull per quantified variable from the leaves that mention it, and `continue`s
past a leaf that mentions no quantified variable (`if bounded.is_empty() {
continue; }`, line ~225). When `allow_empty` is set, a hull with zero members
is accepted. `finite_forall_goal_instances`
(`src/kernel/assumptions/proposition_reasoning.rs:161-214`) then produces zero
instances, and `apply_enumerate` (`src/kernel/proof/object.rs:1148-1163`)
closes the goal after checking those zero instances. The skipped leaf is
never checked, so `forall (k) { (5 <= k and k < 3 implies k == 1) and (x > 0
implies x == 7) }` verifies from `x > 0` alone. The same table is used by the
surface `simp` closure (`src/surface/proof/smart_closures.rs:3336`), so
`simp();` alone proves it; the explicit `enumerate();` tactic proves it too.

The same hole applies to a nested chain: `forall (k) { forall (j) { (5 <= k
and k < 3 implies ...) and (0 <= j and j < 2 implies x == 7) } }` has an
empty hull for `k`, so the `j` leaf is never checked either.

## Reproduction

Pure theorem:

```click
theorem q02(x: int32) {
    requires x > 0;
    ensures forall (k: int32) { (5 <= k and k < 3 implies k == 1) and (x > 0 implies x == 7) } by { simp(); }
}
```

The claim is false at `x == 1`. Observed:

```
$ click verify repro.md
1 selected proof verified          (exit 0)
```

The same with `by { enumerate(); }` also verifies (exit 0). Through a C
function:

```c filename=q07.c
int32 f(int32 x) { return x; }
```
```click
verifying "q07.c";
int32 f(int32 x) {
    requires x > 0;
    ensures forall (k: int32) { (5 <= k and k < 3 implies k == 1) and (x > 0 implies result == 7) };
} by {
    execute();
    simp();
}
```

Observed: `1 selected proof verified`, exit 0, although `f(1) == 1`.

Control: with a non-empty hull (`0 <= k and k < 2` in the first leaf)
the same goal is refused, because the second leaf is then
checked at each enumerated point.

## Intended regression

An mdtest with the pure theorem above (and the `enumerate();` spelling)
expecting `fail`, plus the C-function spelling expecting `fail`, plus the
nested-chain variant. Keep a positive neighbour: the same body with the
unquantified leaf removed, or with `x == 7` added as a `requires`, must still
pass by `simp();`.

## Acceptance criteria

- `finite_forall_ranges_allowing_empty` (or its enumerate consumer) refuses
  the empty hull when any leaf mentions no quantified variable, or
  `apply_enumerate` and the `simp` finite-universal closure check such leaves
  once directly even when the enumeration is empty.
- The three regressions above fail with a prompt refusal; the positive
  neighbours pass; `scripts/check.sh` passes.
