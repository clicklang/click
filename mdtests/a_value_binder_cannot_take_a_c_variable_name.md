# A value binder cannot take a C variable's name

The contract's value binder `s: seg(p, _)` has the parameter `s.n`, and the
C global `s` has the field `s.n`. Before, `owns s.n` read the global while
`requires` and `ensures` read the binder's parameter, so this proof verified
`s.n == 5` although the body sets the global's `n` to 7. A value binder is
refused a C variable's name, as it is a C parameter's.

```c filename=value_binder_named_like_a_global.c
struct S { int32 n; };
struct S s;
void f(int32* p) { s.n = 7; }
```

```click
verifying "value_binder_named_like_a_global.c";

resource seg(p: int32*, n: int32) {
    owns p[0..1];
    fact p[0] == n;
}

void f(int32* p) {
    owns s: seg(p, _);
    owns s.n;
    requires s.n == 5;
    ensures s.n == 5;
} by {
    execute();
    simp();
}
```

```expect
fail: value binder `s` takes the name of a C variable
```
