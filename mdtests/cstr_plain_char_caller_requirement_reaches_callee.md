# Plain char cstr forwarding

`outer` lends the string it views, `cstr_at(src, _)`, to `measure`, which
lends it to `strlen`; each binder's `str.len` is the same length.

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
    views str: click::cstr::cstr_at(src, _);
    ensures result == str.len;
    ensures src[result] == '\0';
} by {
    execute();
    simp();
}
```

`measure` and `outer` verify:

```expect
pass
```
