# `close()` after execution acts on the first open claim

After execution the first `close()` closes `result == 1`. The second closes
`result == n`. An omitted proof tail can close the remaining claims together.

```c filename=solve_after_execution_acts_on_the_first_open_claim.c
int32 f(int32 n) {
    return n;
}
```

```click
verifying "solve_after_execution_acts_on_the_first_open_claim.c";

int32 f(int32 n) {
    requires n == 1;
    ensures result == 1;
    ensures result == n;
} by {
    step_until(function.exit);
    close();
    close();
}
```

```expect
pass
```
