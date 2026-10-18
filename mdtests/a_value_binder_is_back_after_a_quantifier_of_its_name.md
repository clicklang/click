# A value binder is back after a quantifier of its name

Inside `forall (s: int32) { ... }`, `s` is the quantified `int32`. Once the
quantifier's body ends, `s.n` reads the contract's value binder
`s: seg(p, _)` again, whose parameter is 5.

```c filename=a_value_binder_is_back_after_a_quantifi.c
void f(int32* p) { }
```

```click
verifying "a_value_binder_is_back_after_a_quantifi.c";

resource seg(p: int32*, n: int32) {
    owns p[0..1];
    fact p[0] == n;
}

void f(int32* p) {
    owns s: seg(p, _);
    requires s.n == 5;
} by {
    have forall (s: int32) { s == s } by { intro(); simp(); }
    have s.n == 5 by { simp(); }
    execute();
    simp();
}
```

```expect
pass
```
