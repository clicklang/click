# A built-in check refuses an insufficient Integer bound

The Integer reading of `int32` definedness needs both bounds of the exact
result. With only the upper bound, `a - b` may still go below `int32`, so
the C subtraction is refused as a possible signed overflow; compare
[`a_built_in_check_accepts_the_integer_reading_of_its_condition.md`](a_built_in_check_accepts_the_integer_reading_of_its_condition.md).

```c filename=insufficient_bound.c
int difference(int a, int b) { return a - b; }
```

```click
verifying "insufficient_bound.c";

int32 difference(int32 a, int32 b) {
    requires to_integer(a) - to_integer(b) <= 2147483647;
    ensures to_integer(result) == to_integer(a) - to_integer(b);
}
```

```expect
fail: signed overflow
```
