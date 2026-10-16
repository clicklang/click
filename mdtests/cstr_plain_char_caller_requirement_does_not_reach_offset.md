# Plain char cstr forwarding

`outer` views the string at `src`, not at `src + 1`, so the call
`measure(src + 1)` finds no `cstr_at` instance at its argument.

```c filename=measure.c
#include <string.h>

unsigned long measure(const char *src)
{
	return strlen(src);
}

unsigned long outer(const char *src)
{
	unsigned long n = measure(src + 1);
	return n;
}
```

```click
verifying "measure.c";

uint64 measure(const char* src) {
    views str: click::cstr::cstr_at(src, _);
    ensures result == str.len;
    ensures src[result] == '\0';
} by {
    execute();
    simp();
}

uint64 outer(const char* src) {
    views str: click::cstr::cstr_at(src, _);
    ensures result == str.len;
    ensures src[result] == '\0';
} by {
    execute();
    simp();
}
```

`measure` verifies; `outer` is refused at the call:

```expect
fail: call to `measure` needs a held `cstr_at` instance to give `str.len` its value
```
