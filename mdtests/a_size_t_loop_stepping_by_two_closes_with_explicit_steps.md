# A size_t loop stepping by two closes with explicit steps

`last` walks a byte range two at a time with a `size_t` index and reads
`bytes[i + 1]`. The read is in range from the loop condition, `i + 1 <
length`. The back edge owes two linear facts about 64-bit values: the
invariant `i + 2 <= length`, and that `length - i` decreases.

`arithmetic` reads `int32` and `Integer` goals, so each fact is a lemma
proved through `to_integer`: `auto` states the 64-bit premises in Integer
order (the strict loop condition among them), observes the sums and
differences once they are shown not to wrap, and `simp` carries the Integer
conclusion back to the 64-bit order.

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
import click::integer;

verifying "a_size_t_loop_stepping_by_two_closes_with_explicit_steps.c";

theorem step_two(i: uint64, length: uint64) {
    requires i <= length;
    requires to_integer(i + 1u64) < to_integer(length);
    requires length <= 2147483647u64;
    ensures to_integer(i + 2u64) <= to_integer(length) by {
        have to_integer(length) <= to_integer(2147483647u64) by auto();
        have to_integer(i) <= to_integer(length) by auto();
        have to_integer(i) + to_integer(1u64) <= 18446744073709551615 by {
            arithmetic() using { to_integer(i) <= to_integer(length); to_integer(length) <= to_integer(2147483647u64); };
        }
        have to_integer(i + 1u64) == to_integer(i) + to_integer(1u64) by auto();
        have to_integer(i + 1u64) < to_integer(length) by auto();
        have to_integer(i) + to_integer(2u64) <= 18446744073709551615 by {
            arithmetic() using { to_integer(i) <= to_integer(length); to_integer(length) <= to_integer(2147483647u64); };
        }
        have to_integer(i + 2u64) == to_integer(i) + to_integer(2u64) by auto();
        have to_integer(i + 2u64) == to_integer(i + 1u64) + 1 by {
            arithmetic() using {
                to_integer(i + 2u64) == to_integer(i) + to_integer(2u64);
                to_integer(i + 1u64) == to_integer(i) + to_integer(1u64);
            };
        }
        have to_integer(i + 1u64) + 1 <= to_integer(length) by {
            arithmetic() using { to_integer(i + 1u64) < to_integer(length); };
        }
        have to_integer(i + 2u64) <= to_integer(length) by {
            arithmetic() using {
                to_integer(i + 2u64) == to_integer(i + 1u64) + 1;
                to_integer(i + 1u64) + 1 <= to_integer(length);
            };
        }
        simp();
    }
}

theorem step_two_decreases(i: uint64, length: uint64) {
    requires i <= length;
    requires to_integer(i + 2u64) <= to_integer(length);
    requires length <= 2147483647u64;
    ensures to_integer(length - (i + 2u64)) < to_integer(length - i) by {
        have to_integer(length) <= to_integer(2147483647u64) by auto();
        have to_integer(i) <= to_integer(length) by auto();
        have to_integer(i + 2u64) <= to_integer(length) by auto();
        have to_integer(i) + to_integer(2u64) <= 18446744073709551615 by {
            arithmetic() using { to_integer(i) <= to_integer(length); to_integer(length) <= to_integer(2147483647u64); };
        }
        have to_integer(i + 2u64) == to_integer(i) + to_integer(2u64) by auto();
        have to_integer(length - i) == to_integer(length) - to_integer(i) by auto();
        have to_integer(length - (i + 2u64)) == to_integer(length) - to_integer(i + 2u64) by auto();
        have to_integer(length - (i + 2u64)) < to_integer(length - i) by {
            arithmetic() using {
                to_integer(length - (i + 2u64)) == to_integer(length) - to_integer(i + 2u64);
                to_integer(length - i) == to_integer(length) - to_integer(i);
                to_integer(i + 2u64) == to_integer(i) + to_integer(2u64);
            };
        }
        simp();
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
            have to_integer(i + 2u64) <= to_integer(length) by {
                apply(step_two(i, length));
            }
            have to_integer(length - (i + 2u64)) < to_integer(length - i) by {
                apply(step_two_decreases(i, length));
            }
            step(); step();
            simp();
        }
    }
}
```

```expect
pass
```
