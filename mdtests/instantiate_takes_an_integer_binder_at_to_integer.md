# instantiate takes an Integer binder at to_integer

An `Integer` binder takes any `Integer` expression, here a machine parameter
converted with `to_integer`. Known guards propagate through the instance just as for an `int32` binder.

```c filename=instantiate_takes_an_integer_binder_at_to_integer.c
void unused(void) {}
```

```click
verifying "instantiate_takes_an_integer_binder_at_to_integer.c";

function sq(z: Integer) -> Integer { z * z }

theorem conv(x: int32, g: Integer) {
    requires forall (z: Integer) { sq(z) <= g };
    ensures sq(to_integer(x)) <= g by {
        instantiate(forall (z: Integer) { sq(z) <= g }, to_integer(x));
        known();
    }
}

theorem guarded(x: int32, g: Integer) {
    requires forall (z: Integer) { 0 <= z implies sq(z) <= g };
    requires 0 <= to_integer(x);
    ensures sq(to_integer(x)) <= g by {
        have 0 <= (to_integer(x));
        instantiate(forall (z: Integer) { 0 <= z implies sq(z) <= g }, to_integer(x));
        known();
    }
}
```

```expect
pass
```
