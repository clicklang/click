# `snprintf` with a literal format states each character it writes

A call to `snprintf` whose format is a string literal calls a function with
one parameter per conversion. Its contract is written from the format: the
result is the number of characters the format produces, and each character
within the first `size - 1` is stated with the decimal rendering functions of
`click::format`. `decimal_length_n` gives an `n`-digit value's length,
`decimal_digit_of_length` a digit, and `pow10_e` a power of ten.

`".%03u"` is the fraction `string_get_size` in Linux `lib/string_helpers.c`
writes: a `.` and three digits, zero-padded.

```c filename=snprintf_digits.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);

int render(char *buf, unsigned int n)
{
	return snprintf(buf, 8, "%u", n);
}

int fraction(char *tmp, unsigned int remainder)
{
	return snprintf(tmp, 12, ".%03u", remainder);
}
```

```click
import click::format;
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "snprintf_digits.c";

int32 render(char buf[], uint32 n) {
    requires n == 42u32;
    owns buf[0..8];
    ensures result == 2 by {
        execute();
        have format::decimal_length(42u64) == 2u64 by {
            apply(format::decimal_length_2(42u64));
        }
        have result == 2 by {
            simp() using { result == (int32) format::decimal_length((uint64) n); n == 42u32; format::decimal_length(42u64) == 2u64; };
        }
    }
    ensures buf[0] == 52 by {
        execute();
        have (uint64) n == 42u64 by { simp(); }
        have format::decimal_length((uint64) n) == 2u64 by {
            rewrite((uint64) n == 42u64);
            apply(format::decimal_length_2(42u64));
        }
        have format::decimal_digit((uint64) n, 0u64) == 52u8 by {
            rewrite((uint64) n == 42u64);
            apply(format::decimal_digit_of_length(42u64, 2u64, 0u64));
            apply(format::pow10_1());
            simp() using {
                format::decimal_digit(42u64, 0u64) == (uint8) (48u64 + 42u64 / format::pow10(2u64 - 1u64 - 0u64) % 10u64);
                format::pow10(1u64) == 10u64;
            };
        }
        have buf[0] == format::decimal_digit((uint64) n, 0u64) by {
            instantiate(forall (k: uint64) {
                k < format::decimal_length((uint64) n) and k + 1u64 < 8u64 implies buf[k] == format::decimal_digit((uint64) n, k)
            }, 0u64) using { format::decimal_length((uint64) n) == 2u64; };
            simp();
        }
        have buf[0] == 52 by {
            simp() using { buf[0] == format::decimal_digit((uint64) n, 0u64); format::decimal_digit((uint64) n, 0u64) == 52u8; };
        }
    }
}

int32 fraction(char tmp[], uint32 remainder) {
    requires remainder == 5u32;
    owns tmp[0..12];
    ensures result == 4 by {
        execute();
        have (uint64) remainder == 5u64 by { simp(); }
        have format::decimal_length(5u64) == 1u64 by {
            apply(format::decimal_length_1(5u64));
        }
        have format::padded_length((uint64) remainder, 3u64) == 3u64 by {
            rewrite((uint64) remainder == 5u64);
            unfold(format::padded_length(5u64, 3u64));
            simp() using { format::decimal_length(5u64) == 1u64; };
        }
        have result == 4 by {
            simp() using {
                result == (int32) (1u64 + format::padded_length((uint64) remainder, 3u64));
                format::padded_length((uint64) remainder, 3u64) == 3u64;
            };
        }
    }
    ensures tmp[0] == 46 by {
        execute();
        simp();
    }
}
```

```expect
pass
```
