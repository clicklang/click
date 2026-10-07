# `count(R(p))` ignores a transfer of `R(q)` when `q` may equal `p`

## Violated invariant

`count(ticket(p))` is the number of existing units of the population
`ticket(p)`. Two population keys `ticket(p)` and `ticket(q)` denote the same
population whenever `p == q`. A contract transfer of `ticket(q)` must therefore
change, or make unknown, the observed `count(ticket(p))` unless `p != q` is
established. The kernel keys legacy counted populations by their syntactic
`ResourceArguments` and applies a transfer only to the exactly matching key;
`CState::counted_population_sum` (src/kernel/primitives/memory_state.rs:7744)
then sums only entries whose arguments are *proven equal* to the requested ones
and silently excludes entries that are merely *not proven different*. The result
is a false count that verifies.

Responsible code: `apply_counted_population_transitions_with_interface`
(src/kernel/functions.rs:22454, the per-key loop starting near line 22537, and
the `new_count` / `without_counted_population` update near lines 22680-22790)
together with `counted_population_sum`
(src/kernel/primitives/memory_state.rs:7744). The modeled-pthread worker path
reaches the same code through `suspend_verified_worker` and
`WorkerPopulationCount`, so the same false claim verifies across fork/join.

## Reproduction

Sequential form (no runtime selection needed):

```c filename=e101b.c
void spend(void *argument) { }
int run(void *p, void *q) {
    spend(p);
    spend(q);
    return 1;
}
```
```click
verifying "e101b.c";
abstract resource ticket(p: void*);
void spend(void* argument) {
    consumes ticket(argument);
} by { execute(); simp(); }
int32 run(void* p, void* q) {
    consumes ticket(p);
    consumes ticket(q);
    requires count(ticket(p)) == 2;
    ensures count(ticket(p)) == 1;
} by {
    execute();
    simp();
}
```

Observed: `click verify` exits 0 with `2 selected proofs verified`.

The precondition is satisfiable with `p == q` (two units of `ticket(p)` owned,
`count(ticket(p)) == 2`), and in that case both calls consume units of
`ticket(p)` so the true count afterwards is 0, not 1. The verifier cannot prove
`p != q` here (the sibling variant `ensures p != q` is refused with an unclosed
goal), yet it accepts `count(ticket(p)) == 1`.

Fork/join form (`runtime "modeled-pthread"`):
two `pthread_create` workers each `consumes ticket(argument)`, started with `p`
and `q`; after both joins `ensures result == 1 implies count(ticket(p)) == 1`
verifies (exit 0) while the variants `... implies p != q` and
`... implies count(ticket(p)) == 0` are both refused, showing neither the
disequality nor the aliased case is being decided.

## Intended regression

Add `mdtests/population_count_alias_consumption_rejected.md` with the
sequential program above and `expect fail` on `ensures count(ticket(p)) == 1`
(unclosed goal), plus the modeled-pthread variant with
`ensures result == 1 implies count(ticket(p)) == 1` expecting failure. Keep
`mdtests/modeled_pthread_counted_shared_join.md`, which supplies
`requires p != q`, passing.

## Acceptance criteria

- A population transfer keyed on arguments that are not proven different from
  an existing population entry either refuses the transfer (as the authority
  path's "unsupported alias checking" refusal already does for some cases) or
  marks the possibly aliased entries' counts unknown, so `count(...)` on them
  is no longer provable.
- `counted_population_sum` returns `None` when any entry of the same family
  with the same arity is neither proven equal nor proven different from the
  requested arguments.
- The regressions above fail before the fix and pass after; the existing
  `count`/population fixtures and `scripts/check.sh` stay green.
