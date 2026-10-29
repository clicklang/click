# Introducing a typed universal reaches its written body

The uint8 binder supplies its intrinsic range facts without inserting extra
implication goals before the written existential.

```click
theorem typed_witness() {
    ensures forall (a: uint8) {
        exists (k: int32) { to_uint8(to_integer(k)) == to_uint8(to_integer(k)) }
    } by {
        intro();
        witness { k: 0 };
        solve();
    }
}

theorem typed_witness_under_implication() {
    ensures 0 == 0 implies forall (a: uint8) {
        exists (k: int32) { to_uint8(to_integer(k)) == to_uint8(to_integer(k)) }
    } by {
        intro();
        intro();
        witness { k: 0 };
        solve();
    }
}

```

```expect
pass
```
