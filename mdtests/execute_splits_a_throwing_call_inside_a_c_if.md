# `execute()` splits a throwing call inside a C `if`

A maybe-throwing call is a fork, like a C `if`: `execute()` splits it into
`returned` and `threw` arms wherever it sits. Here it sits inside one arm
of a C `if`, after a C `if`, and in straight-line code, and the omitted
proofs of each function close on every path.

```c filename=execute_splits_a_throwing_call_inside_a_c_if.c
int32 helper(int32 x) { return x; }

int32 inside(int32 x) {
    int32 y = 0;
    if (x > 0) {
        y = helper(x);
    }
    return y;
}

int32 after(int32 x) {
    int32 y = 0;
    if (x > 0) {
        y = 1;
    }
    y = helper(x);
    return y;
}
```

```click
verifying "execute_splits_a_throwing_call_inside_a_c_if.c";

int32 helper(int32 x) throws int32 {
    ensures result == x by auto;
    exceptional ensures exception == 7 by auto;
}

int32 inside(int32 x) throws int32 {
    ensures result >= 0;
    exceptional ensures exception == 7;
}

int32 after(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}
```

```expect
pass
```
