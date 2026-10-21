# `snprintf` with a variable format is refused

A format that is not a string literal fixes neither the call's arity nor the
types of its arguments, so Click does not model the call.

```c filename=variable_format.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);

int render(char *buf, const char *fmt, unsigned int n)
{
	return snprintf(buf, 8, fmt, n);
}
```

```click
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "variable_format.c";

int32 render(char buf[], const char* fmt, uint32 n) {
    owns buf[0..8];
    ensures true;
} by {
    execute();
    simp();
}
```

```expect
fail: Click models a call to `snprintf` only with a string-literal format
```
