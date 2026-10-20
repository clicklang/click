# instantiate refuses an Integer binder with a literal argument

`instantiate` takes an `int32` or `uint64` binder. The binder's type is
checked before the argument is read, so the refusal names it, whatever the
argument's spelling, and points to stating the instance as a theorem.

```c filename=instantiate_names_an_integer_binder_it_does_not_take.c
void unused(void) {}
```

```click
verifying "instantiate_names_an_integer_binder_it_does_not_take.c";

theorem t(x: int32) {
    requires forall (z: Integer) { z + 0 == z };
    ensures 5 + 0 == 5 by {
        instantiate(forall (z: Integer) { z + 0 == z }, 5);
    }
}
```

```expect
fail: `z` is an `Integer` binder
```
