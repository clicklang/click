# memcpy reads its source only under a covering resource

The standard-library `memcpy` contract `views` its source, as every external
load needs a covering viewed or owned memory resource. A caller that states
only `viewable(src[0..4])`, which is bounds and readability without read
authority, cannot lend the source, so the call is refused during planning.
The same function with `views src[0..4]` verifies
([`memcpy_const_unsigned_char_source.md`](memcpy_const_unsigned_char_source.md)).

```c filename=memcpy_source_needs_a_covering_resource.c
#include <string.h>
void copy4(unsigned char *dst, const unsigned char *src) { memcpy(dst, src, 4); }
```

```click
verifying "memcpy_source_needs_a_covering_resource.c";
void copy4(uint8* dst, const uint8* src) {
    requires viewable(src[0..4]);
    owns dst[0..4];
    requires separate(memory(dst[0..4]), memory(src[0..4]));
} by { execute(); simp(); }
```

```expect
fail: the required loan backing or binding is missing refused during planning; selected resource `views src[0..4]`
```
