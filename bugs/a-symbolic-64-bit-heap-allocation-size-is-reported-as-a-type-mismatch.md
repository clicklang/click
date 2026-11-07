# A symbolic 64-bit heap allocation size is reported as a type mismatch

Soundness: sound. The refusal is correct: Click models a heap block with a
checked 32-bit extent and does not narrow a symbolic 64-bit size into it.
Only the diagnostic is wrong, so no false claim verifies.

Violated invariant: a refusal names its cause (`bugs/README.md`: inaccurate
or misleading diagnostics). `malloc(n)`, `calloc(n, 1)` and
`realloc(p, n)` with a symbolic `size_t n` report a bare `type mismatch`,
although `n` has the right C type: the cause is the 32-bit heap extent
(`allocation_size_value` in `src/kernel/eval/statements.rs`, documented in
`docs/reference/language/c.md`). An `extern` allocator whose contract writes
`produces allocation(result, bytes)` for a `size_t bytes` reports only
`resource `allocation` argument 1 expects int32, got uint64`, with no
reason or accepted spelling.

Reproduction (unchanged C):

```c
#include <stdlib.h>
#include <stdint.h>

uint8_t *make(size_t n) {
    uint8_t *p = malloc(n);
    return p;
}
```

```click
verifying "a.c";
uint8_t* make(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result != 0;
}
```

reports `step() could not verify C operation: type mismatch` at
`p = malloc(n)`. The extern form (`extern uint8_t* external_alloc(size_t
bytes)` with `produces allocation(result, bytes);`) reports the bare type
error above.

Acceptance criteria:

- The `malloc`, `calloc` and `realloc` refusal for a symbolic 64-bit size
  says that heap blocks have a checked 32-bit extent, that a 64-bit size is
  accepted only where the facts fix it to a constant, and that an upper
  bound is not enough. A non-integer size keeps `type mismatch`.
- The `allocation` byte-count type error for a 64-bit argument names the
  32-bit extent and the accepted spelling, `bytes as int32` under a
  requirement that bounds `bytes`, which verifies.
- mdtests check both messages and the accepted spelling; no verdict changes.
