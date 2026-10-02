# The no-argument attributes take no arguments

An argument list on `unused` is not the modeled form.

```c filename=c_unused_attribute_rejects_arguments.c
__attribute__((unused(1))) int helper(int value);

int32 run(int32 value) {
    return value;
}
```

```click
verifying "c_unused_attribute_rejects_arguments.c";

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail:c_unused_attribute_rejects_arguments.c:1: expected `)`, got `(`
```
