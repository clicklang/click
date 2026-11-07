# A signed specification quotient still owes its overflow exclusion

Specification division is total at a zero divisor, but `MIN / -1` does not
fit `int32`. Like signed `+`, `-` and `*`, the quotient owes that it does not
overflow, so a statement that divides two arbitrary `int32` values is refused
where it is stated.

```click
theorem unguarded(a: int32, b: int32) {
    ensures a / b == a / b;
}
```

```expect
fail: not established: `a != -2147483648 or b != -1`
```
