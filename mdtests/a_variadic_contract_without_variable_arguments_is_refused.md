# A variadic function's contract names its variable arguments

C declares `report` with `...`, so its `extern` contract must name the
variable arguments with a last parameter, `...args`, even when a call passes
none. A contract with only the named parameters is refused.

```c filename=a_variadic_contract_without_variable_arguments_is_refused.c
int report(int code, ...);

int32 run(int32 value) {
    report(value);
    return value;
}
```

```click
verifying "a_variadic_contract_without_variable_arguments_is_refused.c";

extern int32 report(int32 code) {
    ensures result == code;
}

int32 run(int32 value) {
    ensures result == value;
}
```

```expect
fail:`report` is declared with `...` in `a_variadic_contract_without_variable_arguments_is_refused.c`; its `extern` contract names the variable arguments with a last parameter `...args`
```
