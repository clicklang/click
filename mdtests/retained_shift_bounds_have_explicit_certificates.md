# Retained shift bounds have explicit certificate chains

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

```click
theorem nonzero_shift(v: uint64) {
    requires (v >> 32) != 0u64;
    ensures 4294967296u64 <= v by {
        have 1 <= to_integer(v >> 32) by {
            solve() using { to_integer(v >> 32) != 0; };
        }
        have 4294967296 * to_integer(v >> 32) <= to_integer(v) by {
            solve() using { };
        }
        solve() using {
            1 <= to_integer(v >> 32);
            4294967296 * to_integer(v >> 32) <= to_integer(v);
        };
    };
}

theorem zero_shift(v: uint64) {
    requires (v >> 32) == 0u64;
    ensures v < 4294967296u64 by {
        have to_integer(v) <= 4294967296 * to_integer(v >> 32) + 4294967295 by {
            solve() using { };
        }
        solve() using {
            to_integer(v >> 32) == 0;
            to_integer(v) <= 4294967296 * to_integer(v >> 32) + 4294967295;
        };
    };
}

theorem negated_nonzero_shift(v: uint64) {
    requires not ((v >> 32) != 0u64);
    ensures v < 4294967296u64 by {
        have (v >> 32) == 0u64 by {
            normalize() using { not ((v >> 32) != 0u64); };
        }
        have to_integer(v) <= 4294967296 * to_integer(v >> 32) + 4294967295 by {
            solve() using { };
        }
        solve() using {
            (v >> 32) == 0u64;
            to_integer(v) <= 4294967296 * to_integer(v >> 32) + 4294967295;
        };
    };
}


theorem written_negated_observation(v: uint64) {
    requires not (to_integer(v >> 32) != 0);
    ensures v < 4294967296u64;
}

```

```expect
pass
```
