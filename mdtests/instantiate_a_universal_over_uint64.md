# Instantiate a universal over uint64

`instantiate(F, value)` specializes a universal fact at a value of the
binder's type. It took a signed 32-bit binder only, so a fact about every
`size_t` index could be stated and never used. An unsigned 64-bit binder is
now specialized the same way, by a `uint64` argument.

`a_uint64_universal_is_not_instantiated_at_an_int32.md` gives it an
argument of another type.

```click
theorem below_ten(length: uint64, index: uint64) {
    requires forall (k: uint64) { k < length implies k < 10u64 };
    requires index < length;

    ensures index < 10u64 by {
        instantiate(forall (k: uint64) { k < length implies k < 10u64 }, index) using {
            index < length;
        }
    }
}
```

```expect
pass
```
