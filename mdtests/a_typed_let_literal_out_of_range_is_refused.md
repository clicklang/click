# A typed `let` literal outside its type's range is refused

A typed `let` gives an unsuffixed literal the declared type
(`mdtests/a_typed_let_gives_a_literal_its_machine_type.md`), so the literal
must lie in that type's range: 300 is not a `uint8`.

```click
theorem out_of_range() {
    let byte: uint8 = 300;
    ensures to_integer(byte) == 300 by auto();
}
```

```expect
fail: `let byte: uint8` cannot hold 300; a `uint8` lies in 0..=255
```
