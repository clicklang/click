# A recursive call's precondition bounds a decremented argument

The recursive call passes `n - 1` where the contract requires `n <= 100`.
The ambient facts are the contract's `n <= 100` and the branch's `n > 0`;
together they give `n - 1 <= 99`. The one fact lookup reads the upper bound
recorded at `n` and shifts it by the subtracted constant, once `n - 1` is
known not to wrap (`n > 0` rules out `n = INT_MIN`, where `n - 1` is
`INT_MAX`).

A lower bound shifts the same way: `-5 <= n` bounds `n - 1` from below by
`-6`, so `-5 <= n - 1` follows from the branch's `0 < n` (`n - 1 >= 0`).

```c filename=recursive_call_precondition_bounds_a_decremented_argument.c
int32 count(int32 n) {
    if (n <= 0) {
        return 0;
    }
    return count(n - 1);
}
```

```click
verifying "recursive_call_precondition_bounds_a_decremented_argument.c";

int32 count(int32 n) {
    requires n <= 100;
    requires -5 <= n;
    decreases n;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
