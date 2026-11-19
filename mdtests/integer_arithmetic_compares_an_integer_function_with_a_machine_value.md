# Integer arithmetic compares an Integer function with a machine value

Under Integer specification arithmetic a call to a specification `function` declared
`-> Integer` is an Integer operand, so comparing it with a machine value
compares exact Integers: `result == exact_integer(x)` reads
`to_integer(result) == exact_integer(x)`. Under `old` the call stays the Integer it
is rather than being observed again with `to_integer`.

```c filename=integer_arithmetic_compares_an_integer_function_with_a_machine_value.c
int echo(int x) { return x; }
```

```click

verifying "integer_arithmetic_compares_an_integer_function_with_a_machine_value.c";
function exact_integer(v: int32) -> Integer {
    to_integer(v)
}
int32 echo(int32 x) {
    ensures result == exact_integer(x);
    ensures result == old(exact_integer(x));
} by {
    step_until(function.exit);
    unfold(exact_integer(x));
}
```

```expect
pass
```
