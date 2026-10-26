# A typed `let` gives an unsuffixed literal its machine type

`let c: int64 = 5;` is the `int64` 5, not an `int32` that would fail to
match its annotation. Every fixed-width type takes its full range, signed
minimums included. A literal outside the declared type's range is refused
(`mdtests/contract_let_type_mismatch.md`).

```click
theorem typed_literals(x: int64) {
    let a: int8 = -128;
    let b: int16 = 32767;
    let c: int64 = 5;
    let d: uint8 = 255;
    let e: uint16 = 65535;
    let f: uint32 = 4294967295;
    let g: uint64 = 18446744073709551615;
    let h: int64 = -9223372036854775808;
    requires x == c;
    ensures x == c;
    ensures to_integer(a) == -128;
    ensures to_integer(b) == 32767;
    ensures to_integer(f) == 4294967295;
    ensures to_integer(g) == 18446744073709551615;
    ensures to_integer(h) < 0;
    ensures to_integer(d) + to_integer(e) == 65790;
}
```

```expect
pass
```
