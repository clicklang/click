# a summarized loop body's `return` is certified with its value

The positive twin of
[`a_return_inside_a_summarized_loop_body_is_a_function_exit.md`](a_return_inside_a_summarized_loop_body_is_a_function_exit.md):
`f` returns `7` from inside the loop or `5` after it, and the contract names
both. It passes only because the returned path is a certified function exit
carrying `result == 7`; a proof that dropped the path would pass for the wrong
reason, which the negative twin rules out.

```c filename=a_summarized_loop_body_return_is_certified_with_its_value.c
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

```click
verifying "a_summarized_loop_body_return_is_certified_with_its_value.c";

int32 f(int32 n) {
    requires n == 5;
    ensures result == 5 or result == 7;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
    }
    step();
    simp();
}
```

```expect
pass
```
