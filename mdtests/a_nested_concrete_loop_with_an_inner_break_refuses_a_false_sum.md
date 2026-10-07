# A nested concrete loop with an inner `break` refuses a false sum

The negative of
`mdtests/a_nested_concrete_loop_resumes_its_outer_body_after_an_inner_break.md`:
the inner `break` leaves one increment per outer iteration, so `result == 4`
is refused with the sum the execution computed, not with a proof-object
message about the recorded evidence.

```c filename=a_nested_concrete_loop_with_an_inner_break_refuses_a_false_sum.c
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
verifying "a_nested_concrete_loop_with_an_inner_break_refuses_a_false_sum.c";

int32 f(int32 x) {
    ensures result == 4;
} by { execute(); simp(); }
```

```expect
fail: left side evaluated to 3
```
