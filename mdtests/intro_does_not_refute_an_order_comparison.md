# intro does not refute an order comparison

A goal written as the comparison `x < y`, not as `not`, is not opened by
`intro()`: that would make `intro` prove any comparison by refuting its
complement. Prove it directly, or split on the complement with a proof `if`.

```c filename=intro_does_not_refute_an_order_comparison.c
void unused(void) {}
```

```click
verifying "intro_does_not_refute_an_order_comparison.c";

theorem order(x: int32, y: int32) {
    requires x < y;
    ensures x < y by {
        intro();
    }
}
```

```expect
fail: `intro` requires an implication, negation, or universal goal
```
