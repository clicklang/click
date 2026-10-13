# Invariant closure failures discard the checked loop-body trace

Soundness: not soundness. This diagnostic defect does not accept a false proof
or change a verdict. The checked body prefix is missing from a failing trace,
so users cannot inspect the assumptions and facts that led to closure.

The `--trace-proof` contract promises checked tactics and branch facts on the
path to a failure. In this reduction, the body checks the actual decrement and
`to_integer(len) == 0`, then deliberately refuses an incomplete invariant
closure. The error identifies the missing nonnegative ranking fact, but its
trace says `<no checked simple steps recorded on this path>` and
`target tactic has no recorded checked step on a retained path`.

Reproduce from the repository root:

```sh
click verify --trace-proof drain bugs/loop-invariant-closure-trace-drops-body-prefix.md
```

This command should fail. The defect is the missing trace, not the refusal:
`assumption` is not supposed to derive the ranking inequalities from an
equality. The same loss occurs in the original zlib DO16 proof and when a
successful body tactic is selected with `--trace-to` before failed closure.

`apply_close_invariants_body` opens a kernel-owned proof scope and gives its
Surface root a fresh `ProofNode` with no parent. Inspect diagnostic history
across that scope boundary; keep closure certificates bound to their own root.

Acceptance:

- The reduction's failing trace includes the checked body decrement and
  zero-count equation, under its actual loop-head and path assumptions.
- A focused trace to that successful body equation retains its checked path.
- Snapshot identities, source positions and branch guards remain accurate;
  no sibling facts or unverified closure conclusions appear.
- Preserve proof verdicts, source certificates, work budgets and the normal
  diagnostic cap. Retain a persistent prefix rather than copying body history.
- Cover the original zlib scope boundary as well as this small reduction.

```c filename=loop.c
unsigned long drain(unsigned long len) {
    while (len >= 16) { len -= 16; }
    return len;
}
```

```click
target "x86_64-linux-userspace";
verifying "loop.c";
uint64 drain(uint64 len) {
 requires len == 16u64;
 ensures result == 0u64;
} by {
 loop {
  decreases to_integer(len);
  invariant len == 0u64 or len == 16u64;
  initialize by { simp(); }
  preserve by {
   have len == 16u64 by {
    cases {
     len == 0u64 => {
      have not (len >= 16u64) by { rewrite(len == 0u64); normalize(); }
      contradiction(len >= 16u64);
     }
     len == 16u64 => { assumption(); }
    }
   }
   step();
   have len == 0u64 by simp();
   have to_integer(len) == 0 by simp() using { len == 0u64; };
   close_invariants by assumption();
  }
 }
 execute(); simp();
}
```

```expect
fail: assumption
```
