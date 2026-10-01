# A ranked loop whose body branches loses its decrease member

## Violated invariant

A loop with no explicit `preserve` body is summarized by the default closer.
When the body is a two-armed `if` that reaches the back edge on both arms,
the closer should prove each arm's decrease member from that arm's facts.
Instead the loop is refused with a decrease member that follows directly
from those facts:

```
`loop` is missing certified prerequisite (loop ranking measure `state` decreases at the back edge)
(int32 >(value A, 0) is true ⇒ (int32 >(value A, 1) is true ⇒ int32 <(1, value A) is true))
```

The implication is `guard ⇒ (branch ⇒ goal)`, where the goal is the branch
condition written the other way round (`state > 1` against `1 < state`).
With a `uint32` counter whose C is written `0u < state` and `1u < state`,
the goal is the branch condition exactly, `A ⇒ (B ⇒ B)`, and it is still
reported as missing.

## Intended regression

```c
int32 settle(int32 state) {
    while (state > 0) {
        if (state > 1) {
            state = 1;
        } else {
            state = 0;
        }
    }
    return 0;
}
```

```click
int32 settle(int32 state) {
    ensures result == 0;
} by {
    loop {
        decreases state;
    }
    execute();
    simp();
}
```

This should be `pass`, and so should the same loop over `uint32 state`
written with `0u < state` and `1u < state`. A negative counterpart, with the
then-arm assigning `state = state` (no descent), must stay refused.

## Acceptance criteria

- Each arm's ranking member is certified from that arm's own branch fact and
  the guard, or a refused arm is named as a normal `close_invariants`
  failure, not as a missing kernel prerequisite.
- A goal that is literally one of its antecedents always closes.
- No ambient-fact search is added; the arm's path facts are the premises.
