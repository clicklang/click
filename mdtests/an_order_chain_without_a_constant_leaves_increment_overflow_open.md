# an order chain without a constant leaves increment overflow open

The companion of `an_order_chain_to_a_constant_rules_out_increment_overflow.md`
without `j < 1000`. Nothing bounds `j`, so `i` may be `INT32_MAX` and `i + 1`
may overflow: following `i <= j` must not invent a bound.

```c filename=an_order_chain_without_a_constant_leaves_increment_overflow_open.c
int32 next_index(int32 i, int32 j) {
    return i + 1;
}
```

```click
verifying "an_order_chain_without_a_constant_leaves_increment_overflow_open.c";

int32 next_index(int32 i, int32 j) {
    requires 0 <= i;
    requires i <= j;
    ensures result == i + 1 by auto;
}
```

```expect
fail: signed overflow
```
