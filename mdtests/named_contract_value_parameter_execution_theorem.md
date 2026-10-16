# An execution theorem concludes a contract with value parameters

An execution theorem may conclude a contract with value parameters, each
fixed by the conclusion, `Adds(&add3, { amount: 3 })`, and its source facts
may fix their own, `requires Adds(f, { amount: 3 })`. The one checked call
is proved with the target's value parameters at the conclusion's values.

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
    ensures result == x + amount;
}

contract int32 Shifts(int32 x) {
    let offset: int32;
    requires 0 <= x and x <= 1000;
    requires 0 <= offset and offset <= 1000;
    ensures result == x + offset;
}

int32 add3(int32 x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + 3;
} by { execute(); simp(); }

theorem add3_adds_three() executes add3(int32 x) {
    ensures Adds(&add3, { amount: 3 }) by {
        step();
        simp();
    }
}

theorem adds_three_shifts_three(f: int32 (*)(int32)) executes f(int32 x) {
    requires Adds(f, { amount: 3 });
    ensures Shifts(f, { offset: 3 }) by {
        step(Adds);
        simp();
    }
}
```

```expect
pass
```
