# A rejected branch interface loses its checked proof trace

Soundness: not soundness. The invalid interface is correctly rejected, but the
failure omits its checked arm and the written requirement. Pointer-valued
requirements can become unexplained placeholders, blocking proof diagnosis.

`click verify --trace-proof advance branch.click` reports
`proof trace unavailable: no checked path was retained for this failure` for:

```c
// branch.c
int advance(int x) {
    int y;
    if (x >= 0) { y = x; } else { y = 0; }
    return y;
}
```

```click
verifying "branch.c";
int32 advance(int32 x) {
    ensures result == result by {
        step();
        branch ensuring { fact y == x; } then { step(); } else { step(); }
        step(); simp();
    }
}
```

The else arm cannot establish `y == x`. Interface validation returns a plain
error from `apply_branch_interface_with_proof_facts`, without attaching the
failed arm's proof diagnostic or retaining the written requirement. The same
path blocks the nested `match ensuring` in the color-repair proof.

Acceptance: preserve the existing rejection, retain the failed arm's checked
prefix and source requirement through the existing diagnostic APIs, and show
the correct guard for either arm and for a decided one-arm branch. Ordinary
successful joins must not construct diagnostic proof snapshots.
