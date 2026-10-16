# Plain char cstr forwarding

`outer` owns the string `cstr_at(src, _)` and unfolds it to write its first
byte. After the write it holds the bytes, not a string, so the call to
`measure`, which views `cstr_at(src, _)`, has no instance to take the length
from.

```c filename=measure.c
#include <string.h>

unsigned long measure(const char *src)
{
	return strlen(src);
}

unsigned long outer(char *src)
{
	src[0] = 'x';
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

uint64 outer(char* src) {
    owns str: click::cstr::cstr_at(src, _);
    ensures src[result] == '\0';
} by {
    unfold(click::cstr::cstr_at(src, str.len));
    execute();
    simp();
}
```

`measure` verifies; `outer` is refused at the call:

```expect
fail: call to `measure` needs a held `cstr_at` instance to give `str.len` its value
```
