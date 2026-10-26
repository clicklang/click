# Contract Let Type Mismatch

A typed `let` gives an unsuffixed literal the declared type
(`mdtests/a_typed_let_gives_a_literal_its_machine_type.md`), so the literal
must lie in that type's range: 300 is not a `uint8`, and the binding is
refused where it is written.

```c filename=contract_let_type_mismatch.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "contract_let_type_mismatch.c";

int32 identity(int32 x) {
    let byte: uint8 = 300;

    ensures result_value: result == byte;
}
```

```expect
fail: `let byte: uint8` cannot hold 300; a `uint8` lies in 0..=255
```
