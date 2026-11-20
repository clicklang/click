# Variable arguments on a fixed-arity function are refused

`report` is declared without `...`, so its contract has no `...args`
parameter.

```c filename=variable_arguments_on_a_fixed_arity_function_are_refused.c
int report(int code);

int32 run(int32 value) {
    return report(value);
}
```

```click
verifying "variable_arguments_on_a_fixed_arity_function_are_refused.c";

extern int32 report(int32 code, ...args) {
    ensures result == code;
}

int32 run(int32 value) {
    ensures result == value;
}
```

```expect
fail:`report` is not declared with `...` in `variable_arguments_on_a_fixed_arity_function_are_refused.c`, so its `extern` contract has no `...args` parameter
```
