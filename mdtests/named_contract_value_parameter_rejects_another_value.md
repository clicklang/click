# A function meets a parameterized contract only for the values it implements

`add3` adds 3, so `Adds(&add3, { amount: 4 })` does not hold, and the call
passing `&add3` with `k == 4` cannot establish `apply`'s requirement.

```c filename=adds.c
int32 add3(int32 x) {
    return x + 3;
}

int32 apply(int32 (*f)(int32), int32 x, int32 k) {
    int32 result;
    result = f(x);
    return result;
}

int32 caller(int32 x) {
    int32 result;
    result = apply(&add3, x, 4);
    return result;
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

int32 add3(int32 x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + 3;
} by { execute(); simp(); }

int32 apply(int32 (*f)(int32), int32 x, int32 k) {
    requires Adds(f, { amount: k });
    requires 0 <= x and x <= 1000;
    requires 0 <= k and k <= 1000;
    ensures result == x + k;
} by { execute(); simp(); }

int32 caller(int32 x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + 4;
} by { execute(); simp(); }
```

```expect
fail: precondition clause 1 of `apply`
```
