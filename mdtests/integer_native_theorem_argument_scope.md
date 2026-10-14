# Native theorem arguments retain checked Integer conversions

```click
import click::integer;
theorem bounded(z: Integer) {
 requires z >= 0;
 requires z <= 18446744073709551615;
 requires z <= 65520;
 ensures to_uint64(z) <= 65520u64 by {
  have z <= 18446744073709551615 by arithmetic() using { z <= 65520; };
  apply(integer_to_uint64_round_trip(z));
  have to_integer(to_uint64(z)) <= to_integer(65520u64) by arithmetic() using { to_integer(to_uint64(z)) == z; z <= 65520; };
  apply(uint64_to_integer_less_equal_implies_less_equal(to_uint64(z), 65520u64)) using { to_integer(to_uint64(z)) <= to_integer(65520u64); z >= 0; z <= 18446744073709551615; } assumption();
 }
}
```

```expect
pass
```
