# A throwing call inside a C `if` still refuses a false claim

The negative of `mdtests/execute_splits_a_throwing_call_inside_a_c_if.md`:
`helper` throws 7, so the threw arm inside the C `if` cannot establish that
`inside` throws 8.

```c filename=execute_split_inside_a_c_if_refuses_a_false_claim.c
int32 helper(int32 x) { return x; }

int32 inside(int32 x) {
    int32 y = 0;
    if (x > 0) {
        y = helper(x);
    }
    return y;
}
```

```click
verifying "execute_split_inside_a_c_if_refuses_a_false_claim.c";

int32 helper(int32 x) throws int32 {
    ensures result == x by auto;
    exceptional ensures exception == 7 by auto;
}

int32 inside(int32 x) throws int32 {
    ensures result >= 0;
    exceptional ensures exception == 8;
}
```

```expect
fail: did not retain a complete proof for `inside.exceptional_ensures_0`
```
