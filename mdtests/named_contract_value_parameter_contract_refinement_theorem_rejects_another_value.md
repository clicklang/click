# A contract does not refine another at a different value

`Adds(f, { amount: 3 })` does not give `Shifts(f, { offset: 2 })`: unfolding
both binds `amount` to `3` and `offset` to `2`, and the obligation is
refused.

```c filename=adds.c
int32 unused(int32 x) {
    return x;
}
```

```click
verifying "adds.c";

contract int32 Adds(int32 x) {
    let amount: int32;
    requires 0 <= x and x <= 1000;
    requires 0 <= amount and amount <= 1000;
    ensures to_integer(result) == to_integer(x + amount);
}

contract int32 Shifts(int32 x) {
    let offset: int32;
    requires 0 <= x and x <= 1000;
    requires 0 <= offset and offset <= 1000;
    ensures to_integer(result) == to_integer(x + offset);
}

theorem adds_three_shifts_two(f: int32 (*)(int32)) {
    requires Adds(f, { amount: 3 });
    ensures Shifts(f, { offset: 2 }) by {
        unfold(Adds);
        unfold(Shifts);
        solve();
    }
}
```

```expect
fail: could not establish `0 <= x and x <= 1000 and (0 == 0 and 0 == 0) implies 0 <= x and x <= 1000 and (0 == 0 and 0 == 0) and ((let integer_value: Integer = to_integer((x as int32)) + 3; integer_value) <= 2147483647 and (let integer_value: Integer = to_integer((x as int32)) + 3; integer_value) >= -2147483648 and result == (x + 3) implies (let integer_value: Integer = to_integer((x as int32)) + 2; integer_value) <= 2147483647 and (let integer_value: Integer = to_integer((x as int32)) + 2; integer_value) >= -2147483648 and result == (x + 2))`
```
