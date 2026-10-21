# `snprintf` copies a C string the caller views

A `%s` argument is read as a C string: the contract views it as
`click::cstr::cstr_at` and writes its `len` characters. A caller that views
the string passes that view to the call.

```c filename=unit_name.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);

int unit_of(char *buf, const char *name)
{
	return snprintf(buf, 8, "%s", name);
}
```

```click
import click::format;
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "unit_name.c";

int32 unit_of(char buf[], const char* name) {
    owns buf[0..8];
    views s: click::cstr::cstr_at(name, _);
    requires s.len < 4u64;
    ensures result == (int32) s.len by {
        execute();
        simp();
    }
}
```

```expect
pass
```
