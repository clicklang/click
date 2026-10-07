# A nested concrete loop resumes its outer body after an inner `break`

Both loops carry no annotations, so `execute()` runs them concretely. The
inner loop leaves through `break` on its second iteration, and the outer body
resumes at the statement after it: `i = i + 1`, then the outer head again.
The `break` consumes the inner loop's continuation, whose source is the rest
of the outer body alone; the source the next theorem consumes is read from
the kernel's own remaining source at the inner head, which still holds the
outer head and the `return` after it. This was refused as "condition
evidence was recorded with no source statement remaining" when the outer
head's condition came up with the kernel's source exhausted.
`mdtests/a_nested_concrete_loop_with_an_inner_break_refuses_a_false_sum.md`
is the negative.

```c filename=a_nested_concrete_loop_resumes_its_outer_body_after_an_inner_break.c
int32 f(int32 x) {
    int32 i = 0;
    int32 s = 0;
    while (i < 3) {
        int32 j = 0;
        while (j < 3) {
            if (j == 1) break;
            s = s + 1;
            j = j + 1;
        }
        i = i + 1;
    }
    return s;
}
```

```click
verifying "a_nested_concrete_loop_resumes_its_outer_body_after_an_inner_break.c";

int32 f(int32 x) {
    ensures result == 3;
} by { execute(); simp(); }
```

```expect
pass
```
