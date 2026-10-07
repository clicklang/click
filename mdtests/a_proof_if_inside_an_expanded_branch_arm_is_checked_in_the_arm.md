# A proof `if` inside an expanded branch arm is checked in the arm

The stepped form of `nested` in
`mdtests/a_case_split_inside_a_c_if_arm_continues_past_the_arm.md`, as
`click expand` writes it. Under the case `0 <= x`, the inner proof `if`
selects the remaining operand `x < 4` of the C condition `0 <= x && x < 4`.
The outer case supplies `0 <= x`, and each inner arm supplies its explicit
right-operand fact, so a simple step selects the corresponding C path.
Its `then` arm holds another proof `if`, on the nested C condition `y != 0`.

An expanded C branch used to be recognized only when both arms were straight
lines of steps. With the nested `if` in the arm the outer one was read as a
logical case split instead, and its `else` case could not decide the C
condition from the negated conjunction alone: the step at the `if` found two
feasible condition paths. A nested proof `if` in an expanded arm is now
checked inside the arm, as the C branch it spells or as a case split, and a
path that finishes an arm continues past it.

```c filename=a_proof_if_inside_an_expanded_branch_arm_is_checked_in_the_arm.c
int32 nested(int32 x, int32 y) {
    int32 r;
    r = 0;
    if (0 <= x && x < 4) {
        if (y) {
            r = 1;
        }
    }
    return r;
}
```

```click
verifying "a_proof_if_inside_an_expanded_branch_arm_is_checked_in_the_arm.c";

int32 nested(int32 x, int32 y) {
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    if 0 <= x {
        if at(statement(2).entry, x) < at(statement(2).entry, 4) {
            step();
            if at(statement(3).entry, y) != at(statement(3).entry, 0) {
                step();
                step();
                step();
            } else {
                step();
                step();
                step();
            }
        } else {
            step();
            step();
            step();
        }
    } else {
        step();
        step();
        step();
    }
    simp();
}
```

```expect
pass
```
