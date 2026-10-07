# A natural cycle retains both returning and forward goto exits

One checked path returns inside the cycle; another resumes at the forward
label. Both must reach function-exit certification.

```c filename=natural_goto_multiple_exit_labels.c
int32 count_down_or_stop(int32 n) {
again:
    if (n == 0)
        goto done;
    if (n == 1)
        return 7;
    n--;
    goto again;
done:
    return n;
}
```

```click
verifying "natural_goto_multiple_exit_labels.c";

int32 count_down_or_stop(int32 n) {
    requires n >= 0;
    ensures result == 0 or result == 7;
} by {
    loop {
        invariant n >= 0;
        decreases n;
    }
    execute();
    simp();
}
```

```expect
pass
```
