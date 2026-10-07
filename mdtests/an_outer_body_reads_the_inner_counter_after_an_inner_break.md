# An outer body reads the inner counter after an inner `break`

The outer body uses the inner loop's counter after the inner loop breaks, so
the statement after the inner loop runs from the state the `break` left:
`j == 2` on every outer iteration, and `s` sums three of them.
`mdtests/a_nested_concrete_loop_resumes_its_outer_body_after_an_inner_break.md`
is the plain shape.

```c filename=an_outer_body_reads_the_inner_counter_after_an_inner_break.c
int32 f(int32 x) {
    int32 i = 0;
    int32 s = 0;
    while (i < 3) {
        int32 j = 0;
        while (j < 3) {
            if (j == 2) break;
            j = j + 1;
        }
        s = s + j;
        i = i + 1;
    }
    return s;
}
```

```click
verifying "an_outer_body_reads_the_inner_counter_after_an_inner_break.c";

int32 f(int32 x) {
    ensures result == 6;
} by { execute(); simp(); }
```

```expect
pass
```
