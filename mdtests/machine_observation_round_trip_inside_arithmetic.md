# Converting an exact observation back preserves its value inside arithmetic

The conversion returns to the observation's own machine type. Its range follows
from that type, and congruence carries the identity through the surrounding sum.

```click
theorem round_trip_in_sum(value: uint64, delta: uint64) {
    ensures to_uint64(to_integer(value)) + delta == value + delta by {
        normalize();
    }
}
```

```expect
pass
```
