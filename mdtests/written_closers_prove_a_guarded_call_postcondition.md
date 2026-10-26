# the implicit closer proves a guarded call postcondition

The callee's `ensures result == x + 1` reaches the caller as the fact
`x <= 2147483646 implies result == x + 1`: the sum is defined only below the
maximum. The caller's claim is the same equation, and the kernel lowers it
under that same definedness fact. The implicit closer at the end of each
omitted proof closes it.

```c filename=written_closers_prove_a_guarded_call_postcondition.c
int helper(int x);
int by_auto(int x) { return helper(x); }
int by_simp(int x) { return helper(x); }
```

```click
verifying "written_closers_prove_a_guarded_call_postcondition.c";

extern int32 helper(int32 x) { ensures result == x + 1; }

int32 by_auto(int32 x) {
    ensures result == x + 1;
}

int32 by_simp(int32 x) {
    ensures result == x + 1;
}
```

```expect
pass
```
