# instantiate without using names a missing Integer guard

An `Integer` instance's guards are found as exact facts when no `using` list
is written, as an `int32` instance's are. Here `0 <= to_integer(x)` is not a
fact, and the refusal names it.

```c filename=instantiate_without_using_names_a_missing_integer_guard.c
void unused(void) {}
```

```click
verifying "instantiate_without_using_names_a_missing_integer_guard.c";

function sq(z: Integer) -> Integer { z * z }

theorem missing(x: int32, g: Integer) {
    requires forall (z: Integer) { 0 <= z implies sq(z) <= g };
    ensures sq(to_integer(x)) <= g by {
        instantiate(forall (z: Integer) { 0 <= z implies sq(z) <= g }, to_integer(x));
    }
}
```

```expect
fail: `instantiate` without `using` needs each instantiated guard as an exact fact
```
