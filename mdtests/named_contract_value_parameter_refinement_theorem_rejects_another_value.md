# A refinement theorem for one value does not prove another

`add3` adds three, so a theorem concluding `Adds(&add3, { amount: 4 })` is
refused: the obligation `unfold(Adds)` opens binds `amount` to `4`.

```c filename=adds.c
int32 add3(int32 x) {
    return x + 3;
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

int32 add3(int32 x) {
    requires 0 <= x and x <= 1000;
    ensures to_integer(result) == to_integer(x + 3);
} by { execute(); simp(); }

theorem add3_adds_four() {
    ensures Adds(&add3, { amount: 4 }) by {
        unfold(Adds);
        simp();
    }
}
```

```expect
fail: could not establish `0 <= x and x <= 1000 and (0 == 0 and 0 == 0) implies 0 <= x and x <= 1000 and (defined((x + 3)) and result == (x + 3) implies defined((x + 4)) and result == (x + 4))`
```
