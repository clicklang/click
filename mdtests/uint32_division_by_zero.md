# uint32 division by zero

The literal zero refutes the step's nonzero-divisor obligation. The driver
reports division by zero at the operation.

```c filename=uint32_division_by_zero.c
uint32 uint32_division_by_zero() {
    return 1u / 0u;
}
```

```click
verifying "uint32_division_by_zero.c";

uint32 uint32_division_by_zero() {
    ensures no_result: result == 0u32;
}
```

```expect
fail: undefined behavior: division by zero
```
