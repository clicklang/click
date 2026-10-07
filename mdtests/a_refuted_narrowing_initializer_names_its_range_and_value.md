# A refuted narrowing initializer names its range and value

`uint8 y = x` owes `0 <= x <= 255`, and `x == 300` refutes the upper bound.
The store is a prerequisite the statement cannot meet, and its report says
the facts refute the bound rather than that a premise search missed it, or,
as before, that the operation was a `type mismatch`.
`mdtests/a_refuted_return_narrowing_names_its_range_and_value.md` is the same
conversion at a `return`.

```c filename=a_refuted_narrowing_initializer_names_its_range_and_value.c
int32 f(int32 x) { uint8 y = x; return y; }
```

```click
verifying "a_refuted_narrowing_initializer_names_its_range_and_value.c";

int32 f(int32 x) {
    requires x == 300;
    ensures result == 44;
} by { execute(); simp(); }
```

```expect
fail: missing prerequisite (uint8 narrowing upper bound): the facts refute `x <= 255`: [x == 300]
```
