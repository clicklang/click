# Generic `permutation::count` requires the value to match the element type

The element type is inferred from the array argument, and the counted value
must have that same type: an `int32` value is not counted in a `uint8` buffer.

```click
import click::permutation;

predicate mixed_count(bytes: uint8[], x: int32) {
    permutation::count(bytes, 0, 2, x) == 0
}
```

```expect
fail: type parameter `T` is both uint8 and int32
```
