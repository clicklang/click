# A checked execution from a separately built entry certifies in authority mode

The checked execution started from an entry state built separately from the
contract's, differing only in an empty creation ledger. Certification
rebases it onto the contract entry.

```c filename=natural_goto_cycle.c
int32 maybe_stop(int32 flag) {
again:
    if (flag == 0) {
        return 0;
    }
    flag = 0;
    goto again;
}
```

```click
verifying "natural_goto_cycle.c";

int32 maybe_stop(int32 flag) {
    requires flag >= 0;
    ensures result == 0;
} by {
    loop {
        invariant flag >= 0;
        decreases flag;
    }
    simp();
}
```

```expect
pass
```
