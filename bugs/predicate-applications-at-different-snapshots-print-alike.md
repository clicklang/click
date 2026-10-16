# Two predicate applications at different snapshots print alike

Soundness: not soundness. Both applications are checked by their kernel
instances; only the diagnostic hides why one is not the other.

A predicate application with array arguments carries the snapshot each array
is read at. `memcpy`'s postcondition `bytes::equal(destination, 0u64,
old(source), 0u64, bytes)` reads `source` at the call's entry. A caller that
writes `at(copied, bytes::equal(dst, 0u64, src, 0u64, 4u64))` reads `src`
after the call. The two are distinct instances, but a refusal prints the
missing fact and the available call fact as the same text,
`click::bytes::equal(dst, 0u64, src, 0u64, 4u64)`, so the reader cannot see
that the snapshot of `src` is the difference. Only `CLICK_FULL_DIAGNOSTICS=1`
shows it (`snapshot#5` against `snapshot#4` for the `src` argument). The
invariant violated: a diagnostic that lists a required fact as missing does
not print an available, non-interchangeable fact with the same text.

## Reproduction

```c filename=t.c
#include <string.h>
void copy_t(char *dst, const char *src) { memcpy(dst, src, 4); dst[4] = '\0'; }
```

```click
import click::bytes;
verifying "t.c";
void copy_t(char* dst, const char* src) {
    views src[0..4];
    owns dst[0..5];
    requires separate(memory(dst[0..5]), memory(src[0..4]));
    ensures bytes::equal(dst, 0u64, src, 0u64, 4u64);
} by {
    step();
    mark copied;
    step();
    have bytes::equal(dst, 0u64, src, 0u64, 4u64) by {
        transport(at(copied, bytes::equal(dst, 0u64, src, 0u64, 4u64)), bytes::equal(dst, 0u64, src, 0u64, 4u64));
    }
    execute();
    simp();
}
```

Observed on 2026-10-16 on master `14d830db` plus the fixes for
`bare-transport-in-a-have-body-is-unsupported.md` and
`char-argument-to-a-byte-predicate-unfolds-to-converted-reads.md`:
`transport requires a source derivable from its ambient facts`, with
`missing pure fact click::bytes::equal(dst, 0u64, src, 0u64, 4u64)` and the
same text among the available pure facts. The same happens with `unsigned
char` buffers. Found while trying to state the bytes `label_copy` copies
(`examples/label-build-flags`).

## Acceptance

- The refusal shows how the missing application differs from an available
  one with the same predicate and arguments, for example by printing each
  array argument's snapshot (`old(src)` or `at(copied, src)`) when the two
  differ.
- The reproduction is kept as an mdtest whose expected diagnostic names the
  differing snapshot.
- Applications whose instances are equal still print once, as they do now.
