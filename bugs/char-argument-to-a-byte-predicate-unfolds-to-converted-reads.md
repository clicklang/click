# A `char *` argument to a byte predicate unfolds to converted reads

Soundness: soundness-adjacent. No false acceptance is known; one written
predicate application has two meanings depending on how it was introduced,
and the diagnostic prints them identically.

`click::bytes::equal` takes `uint8[]` parameters, and the type checker accepts
a `char *` argument for them. `memcpy`'s postcondition
`bytes::equal(destination, 0u64, old(source), 0u64, bytes)` is instantiated
with the call's `uint8[]` arguments, so its body compares `uint8` loads. A
caller whose buffers are `char *` writes the same postcondition, and its
application unfolds to `(int8)` conversions of those loads. The caller cannot
restate `memcpy`'s own postcondition, and the unclosed-goal diagnostic lists
the call's fact as `click::bytes::equal(dst, 0u64, src, 0u64, 4u64)`, the
same text as the goal. The same function with `unsigned char *` buffers
verifies.

## Reproduction

```c filename=c.c
#include <string.h>
void copy_u(unsigned char *dst, const unsigned char *src) { memcpy(dst, src, 4); }
void copy_c(char *dst, const char *src) { memcpy(dst, src, 4); }
```

```click
import click::bytes;
verifying "c.c";
void copy_u(uint8* dst, const uint8* src) {
    views src[0..4];
    owns dst[0..4];
    ensures bytes::equal(dst, 0u64, src, 0u64, 4u64);
} by { execute(); simp(); }
void copy_c(char* dst, const char* src) {
    views src[0..4];
    owns dst[0..4];
    ensures bytes::equal(dst, 0u64, src, 0u64, 4u64);
} by { execute(); simp(); }
```

Observed on branch `claude/jolly-goodall-6sox13` (master `40d34180` with
`memcpy` reading under `views`), 2026-10-16: `copy_u` verifies; `copy_c` fails
with `unclosed goal click::bytes::equal(dst, 0u64, src, 0u64, 4u64)` while
the pure facts list `click::bytes::equal(dst, 0u64, src, 0u64, 4u64)`.
Unfolding the goal in a `have` after the call shows, under
`CLICK_FULL_DIAGNOSTICS=1`, the goal
`forall (k: uint64) { true and k < 4u64 implies (int8)at(<state A>, *dst[k])
== (int8)at(<state A>, *src[k]) }` against the call's unfolded fact, whose
loads are the same `read<UInt8>` loads without the conversion.

This blocks stating the bytes `label_copy` copies in
`examples/label-build-flags`, whose C takes `char *`
(`design/borrowed-c-strings.md` step 4).

## Acceptance

- `copy_c` verifies, kept as an mdtest beside `copy_u`.
- A predicate application has one meaning for its parameter types, whichever
  pointer type the argument was written with, or the diagnostic shows the
  difference between two applications that are not interchangeable.
- The fix does not change the C or the library contracts.
