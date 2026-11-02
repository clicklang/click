# A failed back edge after a `branch` join blames the else arm

Soundness: not soundness. The verdict is correct: the joined state does not
establish the invariant, and the proof is refused. Only the report misleads.

A `branch` joins its nonreturning arms where the C `if` ends, keeping only what
both arms agree on (docs/reference/tactics/index.md, "Source branches"). When
the loop's back edge then fails to close an invariant from that joined state,
the refusal is presented as a failure of the else arm's last tactic:

- the trace shows `tactic@N: branch (else arm)` and the else arm's step, and
  no join;
- the report says `refused by: \`step\` (simple: a refusal within its
  documented behavior is a bug)`, pointing at the else arm's `step();`;
- the goal is printed over the joined local (`len == 16u64` with no fact about
  `len`), which reads as if the else arm had lost its own assignment.

The report is the same whichever arm actually breaks the invariant, so a user
fixing "the else arm" changes the wrong code.

## Reproduction

`loop.c`:

```c
unsigned long branch_drain(unsigned long len, int flag) { while (len >= 16) { if (flag == 0) { len -= 16; } else { len = 16; } } return len; }
```

`p.click` (the then arm breaks `len == 16u64`; the else arm keeps it):

```click
target "x86_64-unknown-linux-gnu";
verifying "loop.c";
uint64 branch_drain(uint64 len, int32 flag) {
    requires len == 16u64;
    ensures result <= 16u64;
} by {
    loop {
        invariant len == 16u64;
        initialize by assumption();
        preserve by {
            branch { step(); } else { step(); }
        }
    }
    step_until(function.exit); solve();
}
```

`click verify --trace-proof branch_drain p.click` reports the else arm and its
`step()` as above. Swapping the arms' C assignments (so the else arm breaks the
invariant) produces the same else-arm report. Reproduced on master at
252c3c971.

## Acceptance criteria

- A back-edge (or function-exit) obligation that fails after a `branch` join
  is reported at the join, not at either arm's last tactic: the trace shows the
  `branch` as joined, and the refusal is not attributed to a simple `step`.
- The report says the joined state kept only what both arms agree on, and
  points at `branch ensuring { ... }` or a proof `if` (which keeps the cases
  apart) as the way to carry an arm's facts to the back edge.
- Regression: the reproduction above as an expected-failure mdtest whose
  `expect` block pins the join attribution.
