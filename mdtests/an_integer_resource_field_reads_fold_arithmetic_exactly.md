# An `Integer` resource field reads a fold's arithmetic exactly

A fold map's value for a `field total: Integer;` is used where an Integer is
expected, so `x + 1` there is the exact sum `to_integer(x) + 1`: it is
2147483648 for the `int32` `x == INT32_MAX`, and 4294967296 for the `uint32`
`y == UINT32_MAX`, with no overflow and no wrap.

```c filename=tally.c
void create(int x) { }
void create_unsigned(unsigned int y) { }
```

```click
verifying "tally.c";

resource tally() {
    field total: Integer;
}

void create(int32 x) {
    requires x == 2147483647;
    produces model: tally();
    ensures model.total == 2147483648;
} by {
    step_until(function.exit);
    let model = fold(tally(), { total: x + 1 });
    simp();
}

void create_unsigned(uint32 y) {
    requires to_integer(y) == 4294967295;
    produces model: tally();
    ensures model.total == 4294967296;
} by {
    step_until(function.exit);
    let model = fold(tally(), { total: y + 1 });
    simp();
}
```

```expect
pass
```
