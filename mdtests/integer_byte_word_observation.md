# Unsigned byte observations agree with their promoted word

A byte read can retain its 32-bit carrier. The cast identity requires bounds
on that word observation before connecting it to the narrow byte observation.

```click
import click::integer;

theorem byte_word_observation(value: uint8) {
    ensures to_integer(value) == to_integer(value as int32) by {
        have 0 <= value as int32;
        have value as int32 <= 255;
        close() using { 0 <= to_integer(value as int32); to_integer(value as int32) <= 255; };
    }
}
```

```expect
pass
```
