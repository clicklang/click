# Retained call arguments preserve mathematical conditional guards

```click
import click::format;

theorem retained_guard(v: uint64, width: uint64, k: uint64) {
    ensures 48u8 <= format::padded_digit(v, width, 48u8, k) by {
        unfold(format::padded_digit(v, width, 48u8, k));
        if to_integer(k) < to_integer(format::padded_length(v, width) - format::decimal_length(v)) {
            normalize() using { to_integer(k) < to_integer(format::padded_length(v, width) - format::decimal_length(v)); };
        } else {
            apply(format::decimal_digit_lower_bound(v, k - (format::padded_length(v, width) - format::decimal_length(v))));
            solve() using { not (to_integer(k) < to_integer(format::padded_length(v, width) - format::decimal_length(v))); 48u8 <= format::decimal_digit(v, k - (format::padded_length(v, width) - format::decimal_length(v))); };
        }
    }
}
```

```expect
pass
```
