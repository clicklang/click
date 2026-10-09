# A size_t loop stepping by two closes with explicit steps

`last` walks a byte range two at a time with a `size_t` index and reads
`bytes[i + 1]`. The read is in range from the loop condition, `i + 1 <
length`. The back edge owes two linear facts about 64-bit values: the
invariant `i + 2 <= length`, and that `length - i` decreases.

`arithmetic` reads `int32` and `Integer` goals, so each fact is a lemma
proved through `to_integer`: the order bridges carry the 64-bit premises to
Integer order (`uint64_less_than_to_integer` for the strict loop
condition), `uint64_add_to_integer` and `uint64_subtract_to_integer` carry
the sums once they are shown not to wrap, and `uint64_less_equal_of_to_integer`
or `uint64_less_than_of_to_integer` carries the conclusion back.

```c filename=a_size_t_loop_stepping_by_two_closes_with_explicit_steps.c
unsigned char last(const unsigned char *bytes, unsigned long length) {
    unsigned char v = 0;
    for (unsigned long i = 0; i + 1 < length; i += 2) {
        v = bytes[i + 1];
    }
    return v;
}
```

```click
verifying "a_size_t_loop_stepping_by_two_closes_with_explicit_steps.c";

theorem step_two(i: uint64, length: uint64) {
    requires i <= length;
    requires i + 1u64 < length;
    requires length <= 2147483647u64;
    ensures i + 2u64 <= length by {
        have to_integer(length) <= to_integer(2147483647u64) by apply(uint64_less_equal_to_integer(length, 2147483647u64));
        have to_integer(i) <= to_integer(length) by apply(uint64_less_equal_to_integer(i, length));
        have to_integer(i) + to_integer(1u64) <= 18446744073709551615 by {
            arithmetic() using { to_integer(i) <= to_integer(length); to_integer(length) <= to_integer(2147483647u64); }
        }
        have to_integer(i + 1u64) == to_integer(i) + to_integer(1u64) by apply(uint64_add_to_integer(i, 1u64));
        have to_integer(i + 1u64) < to_integer(length) by apply(uint64_less_than_to_integer(i + 1u64, length));
        have to_integer(i) + to_integer(2u64) <= 18446744073709551615 by {
            arithmetic() using { to_integer(i) <= to_integer(length); to_integer(length) <= to_integer(2147483647u64); }
        }
        have to_integer(i + 2u64) == to_integer(i) + to_integer(2u64) by apply(uint64_add_to_integer(i, 2u64));
        have to_integer(i + 2u64) == to_integer(i + 1u64) + 1 by {
            arithmetic() using {
                to_integer(i + 2u64) == to_integer(i) + to_integer(2u64);
                to_integer(i + 1u64) == to_integer(i) + to_integer(1u64);
            }
        }
        have to_integer(i + 1u64) + 1 <= to_integer(length) by {
            arithmetic() using { to_integer(i + 1u64) < to_integer(length); }
        }
        have to_integer(i + 2u64) <= to_integer(length) by {
            arithmetic() using {
                to_integer(i + 2u64) == to_integer(i + 1u64) + 1;
                to_integer(i + 1u64) + 1 <= to_integer(length);
            }
        }
        apply(uint64_less_equal_of_to_integer(i + 2u64, length));
    }
}

theorem step_two_decreases(i: uint64, length: uint64) {
    requires i <= length;
    requires i + 2u64 <= length;
    requires length <= 2147483647u64;
    ensures length - (i + 2u64) < length - i by {
        have to_integer(length) <= to_integer(2147483647u64) by apply(uint64_less_equal_to_integer(length, 2147483647u64));
        have to_integer(i) <= to_integer(length) by apply(uint64_less_equal_to_integer(i, length));
        have to_integer(i + 2u64) <= to_integer(length) by apply(uint64_less_equal_to_integer(i + 2u64, length));
        have to_integer(i) + to_integer(2u64) <= 18446744073709551615 by {
            arithmetic() using { to_integer(i) <= to_integer(length); to_integer(length) <= to_integer(2147483647u64); }
        }
        have to_integer(i + 2u64) == to_integer(i) + to_integer(2u64) by apply(uint64_add_to_integer(i, 2u64));
        have to_integer(length - i) == to_integer(length) - to_integer(i) by apply(uint64_subtract_to_integer(length, i));
        have to_integer(length - (i + 2u64)) == to_integer(length) - to_integer(i + 2u64) by apply(uint64_subtract_to_integer(length, i + 2u64));
        have to_integer(length - (i + 2u64)) < to_integer(length - i) by {
            arithmetic() using {
                to_integer(length - (i + 2u64)) == to_integer(length) - to_integer(i + 2u64);
                to_integer(length - i) == to_integer(length) - to_integer(i);
                to_integer(i + 2u64) == to_integer(i) + to_integer(2u64);
            }
        }
        apply(uint64_less_than_of_to_integer(length - (i + 2u64), length - i));
    }
}

uint8 last(const uint8* bytes, uint64 length) {
    requires length <= 2147483647u64;
    views bytes[0..length];
    ensures result == result;
} by {
    execute_until(loop(0));
    loop {
        decreases length - i;
        views bytes[0..length];
        invariant length <= 2147483647u64;
        invariant i <= length;
        preserve by {
            have i + 2u64 <= length by {
                apply(step_two(i, length));
            }
            have length - (i + 2u64) < length - i by {
                apply(step_two_decreases(i, length));
            }
            step(); step();
            simp();
        }
    }
    execute(); simp();
}
```

```expect
pass
```
