# Machine remainders describe complete chunks and their tail

The full-width divisor must be positive. Narrowing a complete byte prefix
also requires the original length to fit in the nonnegative signed-word range.
Subtracting a positive chunk size preserves the remainder only when the
subtraction is nonnegative.

```click
import click::integer;

theorem tail_bounds(n: uint64, size: uint64) {
    let tail: Integer = truncating_remainder(to_integer(n), to_integer(size));
    requires 0u64 < size;
    ensures n % size <= n by { close() using { 0u64 < size; }; }
    ensures n % size < size by {
        have 0 < to_integer(size) by close();
        have size != 0u64 by {
            have 1 <= to_integer(size) by {
                apply(integer::lt_step_le(0, to_integer(size)));
                close();
            }
            apply(integer::nonzero_from_one(to_integer(size)));
            close();
        }
        apply(integer::uint64_remainder_to_integer(n, size));
        apply(integer::positive_divisor_remainder_upper(to_integer(n), to_integer(size)));
        have tail + 1 <= (to_integer(size) - 1) + 1 by {
            apply(integer::add_right_order(tail, to_integer(size) - 1, 1));
        }
        have tail + 1 <= to_integer(size) by {
            have (to_integer(size) - 1) + 1 == to_integer(size) by close();
            rewrite(to_integer(size), (to_integer(size) - 1) + 1);
            close();
        }
        have tail < to_integer(size) by {
            apply(integer::step_le_lt(tail, to_integer(size)));
        }
        have to_integer(n % size) < to_integer(size) by {
            rewrite(to_integer(n % size), tail);
            close();
        }
        close();
    }
}
theorem complete_prefix(n: uint64) {
    let tail: uint64 = n % 4u64;
    let prefix: uint64 = n - tail;
    let word: uint32 = prefix as uint32;
    let narrowed: int32 = word as int32;
    let length: Integer = to_integer(n);
    let quotient: Integer = truncating_quotient(length, 4);
    let remainder: Integer = truncating_remainder(length, 4);
    requires n <= 2147483647u64;
    ensures (((n - n % 4u64) as uint32 as int32) % 4) == 0 by {
        have tail <= n by close();
        have to_integer(tail) <= length by close();
        apply(integer::uint64_subtract_to_integer(n, tail));
        apply(integer::uint64_remainder_to_integer(n, 4u64));
        apply(integer::truncation_identity(length, 4));
        apply(integer::sum_difference(length, quotient * 4, remainder));
        have to_integer(prefix) == quotient * 4 + 0 by {
            rewrite(to_integer(prefix), length - to_integer(tail));
            rewrite(to_integer(tail), remainder);
            have length - remainder == length + -remainder by close();
            have quotient * 4 + 0 == quotient * 4 by close();
            rewrite(length - remainder, length + -remainder);
            rewrite(quotient * 4 + 0, quotient * 4);
            close();
        }

        // Both narrowing casts preserve the nonnegative prefix.
        have to_integer(prefix) <= length by {
            rewrite(to_integer(prefix), length - to_integer(tail));
            close() using { 0 <= to_integer(tail); };
        }
        have to_integer(prefix) <= 2147483647 by {
            apply(integer::le_transitive(to_integer(prefix), length, 2147483647));
        }
        have to_integer(prefix) <= 4294967295 by {
            apply(integer::le_transitive(to_integer(prefix), 2147483647, 4294967295));
        }
        have to_integer(word) == to_integer(prefix) by close();
        have 0 <= to_integer(word) by close();
        have -2147483648 <= to_integer(word) by {
            apply(integer::le_transitive(-2147483648, 0, to_integer(word)));
        }
        have to_integer(word) <= 2147483647 by close();
        have to_integer(narrowed) == to_integer(word) by close();

        apply(integer::nonnegative_remainder_from_reconstruction(to_integer(prefix), 4, quotient, 0));
        apply(integer::int32_remainder_to_integer(narrowed, 4));
        have to_integer(narrowed % 4) == 0 by {
            rewrite(to_integer(narrowed % 4), truncating_remainder(to_integer(narrowed), 4));
            rewrite(to_integer(narrowed), to_integer(word));
            rewrite(to_integer(word), to_integer(prefix));
            close();
        }
        close();
    }
}
theorem consume_chunk(n: int32) {
    let shorter: Integer = to_integer(n) - 4;
    let quotient: Integer = truncating_quotient(shorter, 4);
    let remainder: Integer = truncating_remainder(shorter, 4);
    requires 4 <= n;
    ensures (n - 4) % 4 == n % 4 by {
        have 0 <= to_integer(n) by {
            apply(integer::le_transitive(0, 4, to_integer(n)));
        }
        have 0 <= shorter by { close() using { 4 <= to_integer(n); }; }
        apply(integer::truncation_identity(shorter, 4));
        apply(integer::nonnegative_dividend_remainder(shorter, 4));
        apply(integer::positive_divisor_remainder_upper(shorter, 4));

        // Restoring the chunk increments the quotient and leaves the residue unchanged.
        apply(integer::equal_add(shorter, quotient * 4 + remainder, 4, 4));
        apply(integer::multiply_add(quotient, 1, 4));
        have shorter + 4 == to_integer(n) by close();
        have (quotient * 4 + remainder) + 4 == (quotient + 1) * 4 + remainder by {
            rewrite((quotient + 1) * 4, quotient * 4 + 1 * 4);
            close();
        }
        have to_integer(n) == (quotient + 1) * 4 + remainder by close();
        apply(integer::nonnegative_remainder_from_reconstruction(to_integer(n), 4, quotient + 1, remainder));

        apply(integer::int32_nonnegative_subtract_within_value_is_defined(n, 4));
        apply(integer::int32_subtract_to_integer(n, 4));
        apply(integer::int32_remainder_to_integer(n - 4, 4));
        apply(integer::int32_remainder_to_integer(n, 4));
        have to_integer((n - 4) % 4) == to_integer(n % 4) by {
            rewrite(to_integer(n % 4), truncating_remainder(to_integer(n), 4));
            rewrite(to_integer((n - 4) % 4), truncating_remainder(to_integer(n - 4), 4));
            rewrite(to_integer(n - 4), shorter);
            close();
        }
        close();
    }
}
theorem short_tail(n: int32) {
    requires 0 <= n;
    requires n < 4;
    ensures n % 4 == n by {
        have to_integer(n) <= 3 by {
            apply(integer::lt_le_predecessor(to_integer(n), 4));
            close();
        }
        apply(integer::nonnegative_remainder_from_reconstruction(to_integer(n), 4, 0, to_integer(n)));
        apply(integer::int32_remainder_to_integer(n, 4));
        close();
    }
}
```

```expect
pass
```
