# A natural goto exit cannot hide division by zero

The existing `loop` keyword also covers a cycle with one checked forward exit
edge. The back edge re-enters `again`; the forward edge resumes at `done`.

```c filename=natural_goto_exit_label.c
int32 count_down(int32 n) {
again:
    if (n == 0)
        goto done;
    n--;
    goto again;
done:
    return 7 / n;
}
```

```click
verifying "natural_goto_exit_label.c";

int32 count_down(int32 n) {
    requires n >= 0;
    ensures result == 0;
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
fail: division by zero
```
