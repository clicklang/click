# `snprintf` states its result's sign and terminator through the result

The contract requires the number of characters the format produces to be at
most `INT_MAX`, and returns that number as `int`, so it also states that the
result is not negative and where the terminator is, read through the result:
at `buf[(uint64) result]` when the output fits, and in the buffer's last byte
when it does not. A caller with a symbolic count, here the decimal length of
an arbitrary `unsigned` and of a C string it views, proves all three from the
call alone, without restating the count.

```c filename=never_negative.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);

int never_negative(char *buf, int len, unsigned int value, char *name)
{
	return snprintf(buf, len, "%u %s", value, name);
}
```

```click
import click::cstr;
import click::format;
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "never_negative.c";

int32 never_negative(char buf[], int32 len, uint32 value, char name[]) {
    requires 1 <= len;
    requires to_integer(format::decimal_length((uint64) value)) + 8 <= 2147483646;
    views cstr::cstr_at(name, 8u64);
    owns buf[0..(uint64) len];
    ensures 0 <= result;
    ensures (uint64) result < (uint64) len implies buf[(uint64) result] == 0u8;
    ensures (uint64) result >= (uint64) len implies buf[(uint64) len - 1u64] == 0u8;
} by {
    have (uint64) len != 0u64;
    step(snprintf, { n1: 8u64 });
}
```

```expect
pass
```
