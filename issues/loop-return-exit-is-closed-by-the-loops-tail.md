# A loop body's `return` is closed by the tactics after the loop

Priority: P2.

## Violated invariant

A proof must not run one tactic list once per path (`AGENTS.md`, "Scalable
verification is a correctness requirement"; the same rule proof `if` and
`match` arms follow by merging). Each function exit is closed where the proof
reaches it: a `branch` arm that returns closes its own exit, and what follows
the `branch` belongs only to the path that continues.

A `return` inside a loop body breaks this. Since #339 the loop rule exports
the returned path as a second exit of the enclosing function, and the tactics
written after the `loop` are run on it as well as on the normal exit. The
tactics written after the `return` inside the loop's `preserve` proof, which
is where the exit is reached, are dropped.

It also breaks expansion. With two exits at one place in the proof and no
source-level branch between them, `click expand` has nowhere to write each
exit's own closing steps, so it fails for these claims, by site and for the
whole claim.

## Reproduction

`mdtests/a_summarized_loop_body_return_is_certified_with_its_value.md` has

```c
int32 f(int32 n) {
    int32 i = 0;
    while (i < n) {
        if (i == 2) {
            return 7;
        }
        i = i + 1;
    }
    return i;
}
```

with `requires n == 5; ensures result == 5 or result == 7;` and the proof
`step(); step(); loop { decreases n - i; invariant i >= 0; invariant i <= n; } step(); simp();`.

The tail runs on both exits. Insert `have result == 5 by simp;` before the
final `simp();`. It is true on the normal exit and false on the returned one,
and verification fails with "`f.contract` path 1, tactic 4: checked outcome
`have` search did not retain a complete proof". Path 1 is the returned path.

The arm's own tactics are dropped. Write the `preserve` proof out with a
proof `if`:

```
preserve by {
    if i == 2 {
        step();
        step();
        simp();
    } else {
        step();
        step();
        step();
    }
}
```

The proof verifies with or without the `simp();` in the returning arm, and
the `have result == 5` failure above is unchanged by it. A `have` in that arm
after the returning steps is refused: "`have` did not verify as a checked
preservation operation. The preservation driver declined it".

Expansion fails. On current master each of these verifies and fails to expand:

```sh
click expand --claim f.contract mdtests/a_summarized_loop_body_return_is_certified_with_its_value.md
click expand mdtests/a_summarized_loop_body_return_is_certified_with_its_value.md:38
click expand mdtests/natural_goto_forward_exit_and_return.md:32
click expand mdtests/search_terminates_by_unmarked_count.md:232
```

The whole-claim form reports "surface/certificate path coverage diverged at
p1: surface has 1 paths but frame certificate has 2"; the by-line form reports
"two execution paths require different tactic expansions at one surface
leaf". `click audit` reports all three claims as site failures.
`search.contract` expanded before #339: the commit before "Certify a return
inside a summarized loop body as a function exit" (`a0207cc76`) expands line
232 and that commit does not.

A proof-level `if` after the loop does separate the exits, verifies, and
expands:

```
loop { ... }
step();
if result == 7 { simp(); } else { have result == 5 by simp; simp(); }
```

It is a workaround, not the fix: the two exits can return the same value, so
no condition the tool invents separates them in general.

## Where the tactics are lost

The mechanism the fix needs exists for `branch`. When an arm reaches function
exit, `advance_focused_execution_arm`
(`src/surface/proof/checked_drivers/proof_execution.rs`) defers each
following tactic with `defer_post_execution_source_tactic`, and the function
boundary runs them on that arm's path only.

A loop is handled in two phases, and the deferred tactics do not cross
between them:

1. Planning runs the `preserve` proof. A path at function exit becomes a
   `CLoopReturnExit` holding a value, a state and pure facts
   (`execution_planning/loop_planning.rs`, the `is_return_exit` branch). The
   tactics deferred on that path stay in the planning-phase presentation.
   `forward_planning.rs` collects the exits per context and passes them to the
   kernel to build the loop rule.
2. Checking applies the rule at the `loop` tactic. The kernel returns one
   `Return` transition per exit, in the order the exits were given
   (`for exit in return_exits` in `src/kernel/loops.rs`).
   `cursor_execution.rs` partitions them into `loop_return_transitions` and
   records each with `record_pending_loop_return`. At the function boundary
   `complete_pending_loop_returns` appends them to the execution's paths, and
   `claim_proofs.rs` runs the context's one deferred list, the tail's, on
   every path.

`CLoopReturnExit` and `PendingLoopReturnPath` are kernel types and cannot hold
proof tactics, so the lists need a surface side table from the planning result
to the checking phase, matched to the pending paths by position.

## Intended change

- A return exit of a loop is closed by the tactics written after the `return`
  in the `preserve` proof's returning arm. They are carried to the function
  boundary and run on that path only.
- When `preserve` is omitted, or the arm writes no closing tactics, the exit
  is closed by an implicit `simp` that belongs to the `loop` tactic, as the
  omitted phases already are.
- The tactics after the `loop` run once, on the normal exit.
- Expansion writes a return exit's closing steps into the returning arm of the
  `preserve` proof, including when it generated that `preserve` proof itself.
  Appending to a nested loop proof after it has been built has no existing
  mechanism; this is the largest part.
- #339's soundness property stays: every returned path is checked against the
  postcondition and the resource obligations, once.

The same applies to a natural cycle's `return` exit. The whole-claim half of
this for a cycle with both a `return` and a forward `goto` is already filed as
`bugs/natural-goto-mixed-return-exit-expansion-loses-path-coverage.md`, with a
test that pins the gap
(`natural_goto_mixed_return_retains_paths_and_reports_expansion_gap`).

## Intended regression

Two mdtests on the function above:

- a passing one whose `preserve` proof closes the returned exit in its arm
  and whose tail holds `have result == 5 by simp;`, which passes only if the
  tail no longer runs on the returned path;
- a failing one whose returning arm states something false of the returned
  exit and is refused there, which fails only if the arm's tactics are used.

And an expansion test that expands every smart site of
`a_summarized_loop_body_return_is_certified_with_its_value.md` and the whole
claim, and rechecks each result.

## Acceptance

- The two mdtests and the expansion test above are in the gate.
- Every `click expand` command in "Reproduction" succeeds and its output
  verifies, and `click audit` reports no site failure for the three claims.
- An expanded proof of such a claim holds no smart tactic and closes the
  returned exit with explicit steps in the `preserve` arm.
- `bugs/natural-goto-mixed-return-exit-expansion-loses-path-coverage.md` is
  resolved or updated to what remains.
- `docs/concepts/loops-and-invariants.md` says where a returning body path is
  closed.
