# A quantified variable hides a value binder of its name

The contract's value binder `s: seg(p, _)` has the parameter `s.n`, which
is 5. Inside `forall (s: int32) { ... }`, `s` is the quantified `int32`,
which has no field `n`, so the claim `s.n == 5` there cannot read the value
binder. Before, `s.n` still read the binder's parameter, and the claim that
every `int32` has an `n` of 5 verified.

```c filename=a_quantified_variable_hides_a_value_bind.c
void f(int32* p) { }
```

```click
verifying "a_quantified_variable_hides_a_value_bind.c";

resource seg(p: int32*, n: int32) {
    owns p[0..1];
    fact p[0] == n;
}

void f(int32* p) {
    owns s: seg(p, _);
    requires s.n == 5;
} by {
    have forall (s: int32) { s.n == 5 } by { simp(); }
    execute();
    simp();
}
```

```expect
fail: could not lower `have` proposition
```
