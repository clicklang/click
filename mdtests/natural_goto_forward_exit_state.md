# A forward goto retains the state used by its return expression

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
    return n + 7;
}
```

```click
verifying "natural_goto_exit_label.c";

int32 count_down(int32 n) {
    requires n >= 0;
    ensures result == 7;
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
