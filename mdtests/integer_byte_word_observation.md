# Unsigned byte observations agree with their promoted word

A byte read can retain its 32-bit carrier. The cast identity requires bounds
on that word observation before connecting it to the narrow byte observation.

```click
import click::integer;

theorem byte_word_observation(value: uint8) {
    ensures to_integer(value) == to_integer(value as int32) by {
        have 0 <= value as int32;
        have value as int32 <= 255;
        arithmetic_certificate rules {
            premise 0: 0 <= to_integer(value as int32) => 0 <= to_integer(value as int32);
            premise 1: to_integer(value as int32) <= 255 => to_integer(value as int32) <= 255;
            integer_cast_identity bounds [0, 1] => to_integer(value) == to_integer(value as int32);
            conclusion 0;
        }
    }
}
```

```expect
pass
```
