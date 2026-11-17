# A contract result cannot prove a false claim about `program::result`

The C parameter and the contract return value have separate bindings.
Returning seven does not establish that the parameter was seven.

```c filename=c_result_parameter_seven.c
int32 seven(int32 result) {
    return 7;
}
```

```click
verifying "c_result_parameter_seven.c";

int32 seven(int32 result) {
    requires 0 <= program::result and program::result <= 100;
    ensures program::result == 7;
}
```

```expect
fail: unclosed goal
```
