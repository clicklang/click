# An `snprintf` call map names the C string a `%s` copies

A `%s` argument is viewed as `click::cstr::cstr_at(aN, _)`, so its length must
come from somewhere. For a local array, such as `tmp` here, nothing the caller
holds supplies it. The call step names it: `step(snprintf(buf, len, "%u%s", ...),
{ s1: cstr_at(tmp, 0u64) })`. The step is written with the C call's format;
the format picks the formatted-output function and is not an argument. The
binder of the `%s` that converts argument `N`, counting from zero, is `sN`.
The named string is checked at the call, from `tmp`'s bytes.

`buf` is owned as `buf[0..(uint64) len]`, the range the contract's `size`
names.

```c filename=snprintf_call_map_names_a_local_c_string.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);

int f(char *buf, int len)
{
	char tmp[12];

	tmp[0] = '\0';
	return snprintf(buf, len, "%u%s", (unsigned int)7, tmp);
}
```

```click
import click::cstr;
import click::format;
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "snprintf_call_map_names_a_local_c_string.c";

int32 f(char buf[], int32 len) {
    requires 9 <= len;
    owns buf[0..(uint64) len];
    ensures result == 1;
} by {
    step();
    step();
    have format::decimal_length(7u64) == 1u64 by {
        apply(format::decimal_length_1(7u64));
    }
    step(snprintf(buf, len, "%u%s", 7u32, tmp), { s1: cstr_at(tmp, 0u64) });
    step();
    have result == (int32) format::decimal_length(7u64) by {
        simp();
    }
    have result == 1 by {
        simp() using { result == (int32) format::decimal_length(7u64); format::decimal_length(7u64) == 1u64; };
    }
}
```

```expect
pass
```
