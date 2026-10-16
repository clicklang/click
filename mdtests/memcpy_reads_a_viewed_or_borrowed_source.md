# memcpy reads a viewed or borrowed source

The standard-library `memcpy` contract owns its destination and views its
source. A caller that only views the source lends that view to the call
(`copy_viewed`). A caller that owns the source lends it as a view for the
call and gets its ownership back afterwards, so it can write the source
again (`copy_then_clear`). Both keep `memcpy`'s byte-equality postcondition.
Overlapping ranges are refused
([`byte_representation_overlapping_copy_rejected.md`](byte_representation_overlapping_copy_rejected.md)).

```c filename=memcpy_reads_a_viewed_or_borrowed_source.c
#include <string.h>
void copy_viewed(unsigned char *dst, const unsigned char *src) {
    memcpy(dst, src, 4);
}
void copy_then_clear(unsigned char *dst, unsigned char *src) {
    memcpy(dst, src, 4);
    src[0] = 0;
}
```

```click
verifying "memcpy_reads_a_viewed_or_borrowed_source.c";
void copy_viewed(uint8* dst, const uint8* src) {
    views src[0..4];
    owns dst[0..4];
    ensures click::bytes::equal(dst, 0u64, src, 0u64, 4u64);
} by { execute(); simp(); }

void copy_then_clear(uint8* dst, uint8* src) {
    owns src[0..4];
    owns dst[0..4];
    ensures src[0] == 0;
} by { execute(); simp(); }
```

```expect
pass
```
