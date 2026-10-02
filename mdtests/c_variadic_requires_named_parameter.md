# A variadic parameter list needs a named parameter

The selected C profile requires at least one named parameter before `...`.

```c filename=c_variadic_requires_named_parameter.c
int report(...);

int32 run(int32 value) {
    return value;
}
```

```click
verifying "c_variadic_requires_named_parameter.c";

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail:c_variadic_requires_named_parameter.c:1: a variadic parameter list (`...`) requires a preceding named parameter
```
