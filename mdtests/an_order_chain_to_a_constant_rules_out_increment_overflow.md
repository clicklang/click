# an order chain to a constant rules out increment overflow

`i <= j` and `j < 1000` together put `i` below 1000, so `i + 1` cannot
overflow. No fact bounds `i` by a constant directly: the one standard overflow
check follows the chain of order facts out of `i` until it reaches a constant.
`an_order_chain_without_a_constant_leaves_increment_overflow_open.md` is the
same function with the constant removed.

```c filename=an_order_chain_to_a_constant_rules_out_increment_overflow.c
int32 next_index(int32 i, int32 j) {
    return i + 1;
}
```

```click
verifying "an_order_chain_to_a_constant_rules_out_increment_overflow.c";

int32 next_index(int32 i, int32 j) {
    requires 0 <= i;
    requires i <= j;
    requires j < 1000;
    ensures result == i + 1 by auto;
}
```

```expect
pass
```
