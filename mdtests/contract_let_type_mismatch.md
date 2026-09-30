# Contract Let Type Mismatch

```c filename=contract_let_type_mismatch.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "contract_let_type_mismatch.c";

int32 identity(int32 x) {
    let byte: uint8 = 300;

    ensures result_value: result == byte by auto;
}
```

```expect
fail: let binding `byte` evaluated to `300` of type `int32`, which does not match the declared type `uint8`
```
