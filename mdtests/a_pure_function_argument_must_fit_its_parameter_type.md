# A pure-function argument must fit its parameter type

A literal argument converts implicitly to its parameter's type only when it
is a value of that type. `256` is no `uint8`, so `byte_plus_one(256)` is
refused rather than reaching the function as `0`; the conversion is written
as `(uint8) 256` when the wrap is meant.

```click
function byte_plus_one(word: uint8) -> int32 { word + 1 }
theorem implicit_wrap() {
    ensures byte_plus_one(256) == 1 by {
        unfold(byte_plus_one(256)); normalize();
    }
}
```

```expect
fail: function `byte_plus_one` argument 0: `256` is not a value of uint8
```
