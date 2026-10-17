# `execute()` in a `branch` arm blames the path, not the arm

Soundness: not soundness. The proof is refused correctly; the reason given is
not the reason.

## Violated invariant

A diagnostic reports the actual cause of a refusal (CLAUDE.md). An arm of a
proof `branch` must stop at the shared continuation, so it can never reach
the function exit. `step()` past that point is refused with a message that
says so:

```
`step()` ran past the end of its branch body; an arm of `branch` must stop
at the shared continuation
```

`execute()` inside the same arm is refused for the same reason, but its
message says there is no path to the function exit at all:

```
`execute()` found no checked path from this frontier to function exit
```

The same `execute()` on the linear proof line reaches the exit and the proof
verifies, so a user reads this as a verifier failure on a valid path rather
than as a rule about `branch` arms. The message comes from the
`SmartExecute` arm of `apply_frontier_source_tactic`
(`src/surface/proof/checked_drivers/proof_execution.rs`), which every
execution context shares; the arm-specific wording lives in
`src/surface/proof/cursor_execution.rs`.

## Reproduction

```c filename=f.c
void mark_one(int32 a[], int32 n, int32 i, int32 m, int32 c) {
    if (c) {
        a[i] = 1;
    }
}
```

```click
verifying "f.c";

void mark_one(int32 a[], int32 n, int32 i, int32 m, int32 c) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires m != i;
    requires n <= 1073741823;
    owns a[0..n];
    ensures a[m] == old(a[m]);
} by {
    mark entry;
    branch {
        execute();
    } else {
        execute();
    }
    simp();
}
```

Observed on `master` at `00d053a34`: `execute()` found no checked path from
this frontier to function exit. With `execute(); simp();` and no `branch`,
the same function verifies.

## Intended regression

An mdtest with the program above that expects the refusal to say that an arm
of `branch` must stop at the shared continuation, as the `step()` refusal
does.

## Acceptance criteria

- `execute()` in a `branch` arm is refused with a message naming the arm's
  shared-continuation limit.
- `execute()` on the linear proof line and `execute()` that finds no path
  in other contexts keep their current messages.
- The mdtest above is in the gate.
