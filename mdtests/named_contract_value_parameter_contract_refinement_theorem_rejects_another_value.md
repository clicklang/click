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
    ensures result == x + amount;
}

contract int32 Shifts(int32 x) {
    let offset: int32;
    requires 0 <= x and x <= 1000;
    requires 0 <= offset and offset <= 1000;
    ensures result == x + offset;
}

theorem adds_three_shifts_two(f: int32 (*)(int32)) {
    requires Adds(f, { amount: 3 });
    ensures Shifts(f, { offset: 2 }) by {
        unfold(Adds);
        unfold(Shifts);
        simp();
    }
}
```

```expect
fail: could not establish `0 <= x and x <= 1000 and (0 == 0 and 0 == 0) implies 0 <= x and x <= 1000 and (0 == 0 and 0 == 0) and (result == (x + 3) implies result == (x + 2))`
```
