# The implicit tail in a proof `if` arm splits alias cases inside a C `if`

The alias split of
`mdtests/execute_in_a_proof_if_arm_splits_a_loads_alias_cases.md`, reached
inside the arm of a C `if`: the tail that ends the `buf == 0` false arm
splits on each alias case, and each case escapes the C arm and runs to the
function exit on its own.

```c filename=execute_in_a_proof_if_arm_splits_alias_cases_inside_a_c_if.c
int32 f(int32 u, int32 w) {
    int32 r;
    int32* buf;
    buf = malloc(16);
    if (buf == 0) {
        return 0;
    }
    buf[0] = 3;
    buf[u] = 7;
    r = 1;
    if (w > 0) {
        r = buf[0];
    }
    free(buf);
    return r;
}
```

```click
verifying "execute_in_a_proof_if_arm_splits_alias_cases_inside_a_c_if.c";

int32 f(int32 u, int32 w) {
    requires 0 <= u;
    requires u < 4;
    ensures result == 0 or result == 1 or result == 3 or result == 7;
} by {
    step();
    step();
    step();
    if buf == 0 {
    } else {
    }
}
```

```expect
pass
```
