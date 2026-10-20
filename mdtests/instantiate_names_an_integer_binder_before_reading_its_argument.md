# instantiate refuses an Integer binder with a `to_integer` argument

`instantiate` takes an `int32` or `uint64` binder. The binder's type is
checked before the argument is read, so the refusal names it, whatever the
argument's spelling, and points to stating the instance as a theorem.

```c filename=instantiate_names_an_integer_binder_before_reading_its_argument.c
void unused(void) {}
```

```click
verifying "instantiate_names_an_integer_binder_before_reading_its_argument.c";

theorem t(x: int32) {
    requires forall (z: Integer) { z + 0 == z };
    ensures to_integer(x) + 0 == to_integer(x) by {
        instantiate(forall (z: Integer) { z + 0 == z }, to_integer(x));
    }
}
```

```expect
fail: `z` is an `Integer` binder
```
