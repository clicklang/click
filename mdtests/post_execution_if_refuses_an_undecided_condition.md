# A post-execution `if` refuses a condition a path does not decide

On the path where `a > b` is false, `old(a) >= old(b)` follows from the
`requires` only by a case split, which the `if` does not search for, so the
`if` is refused at the `if`. A `have` stating the condition before it decides it
(`post_execution_if_reads_an_earlier_have.md`).

```c filename=pick_undecided.c
int32 pick(int32 a, int32 b) {
    if (a > b) {
        return a;
    }
    return b;
}
```

```click
verifying "pick_undecided.c";

int32 pick(int32 a, int32 b) {
    requires a > b or a == b;
    ensures result >= a;
} by {
    execute();
    if old(a) >= old(b) {
        have result == a;
    } else {
        have result == b;
    }
}
```

```expect
fail: focused outcome does not decide the post-execution `if` condition
```
