# A written pure-function argument conversion is modulo its parameter type

A conversion that can change a value is written. `256 as uint8` converts
`256` to the `uint8` parameter as C converts, modulo 2^8, so it reaches
`byte_plus_one` as `0`. The false claim that it arrives as `256` is refused.
Without the written cast, `byte_plus_one(256)` is refused where it is read:
`256` is no `uint8` (`a_pure_function_argument_must_fit_its_parameter_type.md`).

```click
function byte_plus_one(word: uint8) -> int32 { word + 1 }
theorem wraps() {
    ensures byte_plus_one(256 as uint8) == 1 by {
        unfold(byte_plus_one(256 as uint8)); normalize();
    }
}
theorem out_of_range() {
    ensures byte_plus_one(256 as uint8) == 257 by {
        unfold(byte_plus_one(256 as uint8)); normalize();
    }
}
```

```expect
fail: `out_of_range.ensures_0` proof step tactic 1: `normalize` goal did not normalize to true
```
