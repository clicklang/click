# Unsigned byte observations agree with their promoted word

A byte read can retain its 32-bit carrier. The cast identity requires bounds
on that word observation before connecting it to the narrow byte observation.

```click
theorem byte_word_observation(value: uint8) {
    ensures to_integer(value) == to_integer((int32)value) by {
        have 0 <= (int32)value by { simp(); }
        have (int32)value <= 255 by { simp(); }
        apply(int32_less_equal_to_integer(0, (int32)value));
        apply(int32_less_equal_to_integer((int32)value, 255));
        arithmetic_certificate special {
            premise 0: 0 <= to_integer((int32)value) => 0 <= to_integer((int32)value);
            premise 1: to_integer((int32)value) <= 255 => to_integer((int32)value) <= 255;
            integer_cast_identity bounds [0, 1] => to_integer(value) == to_integer((int32)value);
            conclusion 0;
        }
    }
}
```

```expect
pass
```
