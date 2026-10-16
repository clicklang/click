# Copied bytes stated through `result` need an explicit `transport`

`label_copy`'s pattern returning the count: `memcpy(dst, src, n)`, the
terminator at `dst[n]`, `return n`, and the copied bytes stated over
`result`. The smart closer transports a goal from earlier recorded points,
but a goal naming `result` can be read only at function exit, so it has no
earlier source to carry the call's fact from, and the search misses
promptly. The same claim with the count named, or with an explicit
`transport` of `memcpy`'s postcondition to a `have` over `n`
(`memcpy_then_terminator_keeps_copied_bytes.md`), verifies. The refusal
names the unclosed claim; it does not rest on the supplemental memory-history
walk, which stops at the terminator store without the guard `k < n`.

```c filename=copy.c
#include <string.h>
unsigned long copy_r(char *dst, const char *src, unsigned long n) { memcpy(dst, src, n); dst[n] = '\0'; return n; }
```

```click
import click::bytes;
verifying "copy.c";
uint64 copy_r(char* dst, const char* src, uint64 n) {
    views src[0u64..n];
    owns dst[0u64..n + 1u64];
    requires n < 32u64;
    requires separate(memory(dst[0u64..n + 1u64]), memory(src[0u64..n]));
    ensures bytes::equal(dst, 0u64, src, 0u64, result);
} by { execute(); simp(); }
```

```expect
fail: checked outcome `simp` search did not retain a complete proof for `copy_r.ensures_0`
```
