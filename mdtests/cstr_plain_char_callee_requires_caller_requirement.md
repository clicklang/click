# Plain char cstr forwarding

`outer` holds no string at `src`, so the call to `measure`, whose contract
views `cstr_at(src, _)`, has no instance to take the length from.

```c filename=measure.c
#include <string.h>

unsigned long measure(const char *src)
{
	return strlen(src);
}

unsigned long outer(const char *src)
{
	unsigned long n = measure(src);
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
