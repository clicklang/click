# `snprintf` counts the characters that do not fit

`snprintf(buf, 2, "%u", 123u)` writes `1` and a terminator, and returns 3,
the number of characters the format produces (C11 7.21.6.5p3). When the
output does not fit, the contract places the terminator in the buffer's last
byte.

```c filename=clipped.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);

int clipped(char *buf)
{
	return snprintf(buf, 2, "%u", 123u);
}
```

```click
import click::format;
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "clipped.c";

int32 clipped(char buf[]) {
    owns buf[0..2];
    ensures result == 3 by {
        execute();
        have format::decimal_length(123u64) == 3u64 by {
            apply(format::decimal_length_3(123u64));
        }
        have result == 3 by {
            simp() using { result == (int32) format::decimal_length(123u64); format::decimal_length(123u64) == 3u64; };
        }
    }
    ensures buf[1] == 0 by {
        execute();
        have format::decimal_length(123u64) == 3u64 by {
            apply(format::decimal_length_3(123u64));
        }
        have format::decimal_length(123u64) >= 2u64 by {
            simp() using { format::decimal_length(123u64) == 3u64; };
        }
        simp();
    }
}
```

```expect
pass
```
