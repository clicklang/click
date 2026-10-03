# `sizeof` of an array expression is rejected

An array operand does not decay under `sizeof`, and whole-array sizes of expressions are not modeled.

```c filename=c_sizeof_array_expression_rejected.c
int32 size(int32 value) {
    int32 values[3];
    return sizeof(values);
}
```

```click
verifying "c_sizeof_array_expression_rejected.c";

```

```expect
fail:c_sizeof_array_expression_rejected.c:3: `sizeof` of an expression requires a modeled scalar or pointer operand
```
