# A call through a pointer needs the parameterized contract attached to it

Without `requires Adds(f, { amount: k })`, nothing is known about what `f`
does, so the call through it is refused.

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
    result = apply(&add3, x, 3);
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
    requires 0 <= x and x <= 1000;
    requires 0 <= k and k <= 1000;
    ensures result == x + k;
} by { execute(); simp(); }

int32 caller(int32 x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + 3;
} by { execute(); simp(); }
```

```expect
fail: cannot verify call through function pointer `f`
```
