# Signed-character C-string requirements reach a callee

`outer` lends its borrowed signed-character string `cstr_at(src, _)` to
`measure`, which lends it to `strlen` through a `const char *` cast.

```c filename=measure.c
#include <string.h>

unsigned long measure(const signed char *src)
{
	return strlen((const char*)src);
}

unsigned long outer(const signed char *src)
{
	unsigned long n = measure(src);
	return n;
}
```

```click
verifying "measure.c";

uint64 measure(const int8* src) {
    views str: click::cstr::cstr_at(src, _);
    ensures result == str.len;
    ensures src[result] == '\0';
} by {
    execute();
    simp();
}

uint64 outer(const int8* src) {
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
