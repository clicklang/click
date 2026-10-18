# Integer arithmetic compares an Integer function with a machine value

Under `arithmetic "integer";` a call to a specification `function` declared
`-> Integer` is an Integer operand, so comparing it with a machine value
compares exact Integers: `result == exact(x)` reads
`to_integer(result) == exact(x)`. Under `old` the call stays the Integer it
is rather than being observed again with `to_integer`.

```c filename=integer_arithmetic_compares_an_integer_function_with_a_machine_value.c
int echo(int x) { return x; }
```

```click
arithmetic "integer";

verifying "integer_arithmetic_compares_an_integer_function_with_a_machine_value.c";
function exact(v: int32) -> Integer {
    to_integer(v)
}
int32 echo(int32 x) {
    ensures result == exact(x);
    ensures result == old(exact(x));
} by {
    execute();
    unfold(exact(x));
}
```

```expect
pass
```
