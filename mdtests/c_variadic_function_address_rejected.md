# The address of a variadic function is rejected

A function pointer carries a fixed modeled signature. Taking the address of
a variadic function would drop its variable arguments from that signature.

```c filename=c_variadic_function_address_rejected.c
int report(int code, ...);

int32 run(int32 value) {
    int (*callback)(int code) = report;
    return value;
}
```

```click
verifying "c_variadic_function_address_rejected.c";

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail:c_variadic_function_address_rejected.c:4: variadic function `report` has no modeled variable-argument signature; function-address uses are not supported
```
