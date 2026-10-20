# A step after `instantiate` closes `false` reports "no source goal"

Soundness: not soundness. Nothing false is accepted: the theorem below is
true, and the failure is a refusal. The refusal is an internal invariant
message, blamed on a step that succeeded, for a script whose equivalent with
the universal as a requirement verifies.

The violated invariant: a tactic that closes the current goal leaves the
script in a state the next tactic can be checked against (or refused with a
user-level reason, such as no goal remaining); an internal bookkeeping
message never reaches the user. After `intro()` of `not (forall ...)`, the
goal is `false` with the universal as a fact. `instantiate` of that fact at
`1` yields `1 == 0`, which evaluates to false and closes `false`. Any later
step other than `assumption()` (`contradiction(1 == 0)`, `normalize()`,
`arithmetic()`) then fails with "completed application has no source goal",
reported at the `instantiate` line. The suspected place is the completed-goal
bookkeeping in `src/surface/proof/proof_object/scope.rs`
(`retain_completed_goal`).

```c filename=z.c
void unused() {}
```

```click
verifying "z.c";

theorem t(n: int32) {
    ensures not (forall (x: int32) { x == 0 }) by {
        intro();
        instantiate(forall (x: int32) { x == 0 }, 1);
        contradiction(1 == 0);
    }
}
```

`click verify` prints:

```text
proof error:
  completed application has no source goal

tactic@6:
  instantiate(forall (x: int32) { x == 0 }, 1);
goal: false
refused by: `instantiate` (simple: a refusal within its documented behavior is a bug)
see: click docs instantiate
```

Controls:

- Deleting `contradiction(1 == 0);` verifies, and replacing it with
  `assumption();` verifies.
- The same two steps with the universal as a requirement verify:

  ```click
  verifying "z.c";

  theorem t(n: int32) {
      requires forall (x: int32) { x == 0 };
      ensures false by {
          instantiate(forall (x: int32) { x == 0 }, 1);
          contradiction(1 == 0);
      }
  }
  ```

The two paths also disagree on whether `instantiate` closed the goal. The
[reference](../docs/reference/tactics/index.md#universal-instantiation) says
"If the conclusion is the goal, the goal closes unless other written steps
follow". The requirement version follows that: replacing
`contradiction(1 == 0);` with `normalize();` fails with "`normalize` goal did
not normalize to true" against `goal: false`, so the goal stayed open for the
later step. After `intro()`, the goal closes although a step follows.

## Acceptance criteria

- The reproduction verifies, as the requirement version does, or is refused
  with a user-level reason pointing at `contradiction(1 == 0);`. It never
  prints "completed application has no source goal".
- `instantiate` after `intro()` follows the documented rule, as
  `instantiate` of a requirement does: with later written steps, the goal
  stays open for them.
- A regression keeps the source pattern: `intro()` of `not (forall ...)`,
  `instantiate` at a counterexample, then `contradiction(...)`.
