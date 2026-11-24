# An operation identity bound outside its type is refused

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `close() using { ... }`.

```c filename=an_operation_identity_bound_outside_its_type_is_refused.c
unsigned decrement(unsigned x) { return x - 1u; }
```

```click
verifying "an_operation_identity_bound_outside_its_type_is_refused.c";
uint32 decrement(uint32 x) {
    ensures to_integer(result) == to_integer(x) - 1;
} by {
    step_until(function.exit);
    have -1 <= to_integer(old(x)) - 1;
    have to_integer(old(x)) - 1 <= 4294967295;
    close() using { -1 <= to_integer(old(x)) - 1; to_integer(old(x)) - 1 <= 4294967295; };
}
```

```expect
fail: solve
```
