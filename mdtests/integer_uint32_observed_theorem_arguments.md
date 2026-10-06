# Checked Integer theorem arguments from machine observations

Unsigned observations retain their full range. Mathematical parameters with
colliding names are substituted simultaneously, and observations of unsigned
machine expressions preserve wrapping semantics.

```click
theorem zero_difference(a: Integer, b: Integer) {
    requires a == b;
    ensures a - b == 0 by { arithmetic() using { a == b; } }
}

theorem native_observations(a: uint32, b: uint32) {
    requires to_integer(b) == to_integer(a);
    ensures to_integer(b) - to_integer(a) == 0 by {
        apply(zero_difference(to_integer(b), to_integer(a))) using { to_integer(b) == to_integer(a); }
    }
}

function observation(a: uint32) -> Integer { to_integer(a) }

theorem opaque_observation_argument(a: uint32) {
    ensures observation(a) - observation(a) == 0 by {
        apply(zero_difference(observation(a), observation(a))) using { observation(a) == observation(a); }
    }
}

theorem wrapped_observation(a: uint32) {
    ensures to_integer(a + 1u32) - to_integer(a + 1u32) == 0 by {
        apply(zero_difference(to_integer(a + 1u32), to_integer(a + 1u32))) using { to_integer(a + 1u32) == to_integer(a + 1u32); }
    }
}
```

```expect
pass
```
