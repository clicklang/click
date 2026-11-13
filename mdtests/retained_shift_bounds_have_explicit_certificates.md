# Retained shift bounds have explicit certificate chains

The zero and nonzero guards use the same operation bounds as the native shift.
The explicit links isolate operation-bound discovery from certificate checking.

```click
theorem nonzero_shift(v: uint64) {
    requires (v >> 32) != 0u64;
    ensures 4294967296u64 <= v by {
        have 1 <= to_integer(v >> 32) by {
            arithmetic_certificate {
                excluded_bound 0: to_integer(v >> 32) != 0 => 1 <= to_integer(v >> 32);
                conclusion 0;
            }
        }
        have 4294967296 * to_integer(v >> 32) <= to_integer(v) by {
            arithmetic_certificate {
                operation_bound => 4294967296 * to_integer(v >> 32) <= to_integer(v);
                conclusion 0;
            }
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
            arithmetic_certificate {
                operation_bound => to_integer(v) <= 4294967296 * to_integer(v >> 32) + 4294967295;
                conclusion 0;
            }
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
            arithmetic_certificate {
                operation_bound => to_integer(v) <= 4294967296 * to_integer(v >> 32) + 4294967295;
                conclusion 0;
            }
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
