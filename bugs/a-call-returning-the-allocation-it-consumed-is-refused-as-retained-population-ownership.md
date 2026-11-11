# A call returning the allocation it consumed is refused as retained population ownership

Soundness: incomplete. A valid call is refused; nothing false is accepted.
The refusal names population bookkeeping (`population helper retained
ownership`) that the program does not use, so the diagnostic is also
misleading.

A callee that consumes `allocation(p, bytes)`, states `ensures result == p`,
and produces `allocation(result, bytes)` gives the caller back the block it
was lent. The call continues the allocation
(`allocation_continuity` is `Same` in `apply_verified_heap_allocation_delta`,
`src/kernel/functions.rs`). The caller should then hold the token at `q` (equal
to `p`) and may free it. Instead the call is refused when the population
ledger finishes the call (`finish_call` in the population-helper branch of
the call application, `functions.rs`, message
`population helper retained ownership: population control, members or an
anchor would be discarded at scope exit`).

The same contract without `ensures result == p` verifies: the call then
retires `p`'s allocation and returns a possibly different block, which the
caller frees. Only the proven-same continuity path is refused. The block's
extent format does not matter: the `size_t` version
(`allocation(p, n * 4u64)` over `malloc(n * sizeof(uint32_t))`) gives the same
refusal once a sidecar can state a 64-bit token (heap extents stage 3). The
`int32` reproduction below is refused the same way on master e547bb864.

## Reproduction

```c filename=pass_through.c
#include <stdint.h>
#include <stdlib.h>

uint32_t *touch(uint32_t *p, int n) {
    return p;
}

int caller(int n) {
    uint32_t *p = malloc(n * 4);
    if (p == 0) {
        return 0;
    }
    uint32_t *q = touch(p, n);
    free(q);
    return 1;
}
```

```click
verifying "pass_through.c";

uint32_t* touch(uint32_t* p, int32 n) {
    requires 1 <= n and n <= 1000;
    consumes allocation(p, n * 4);
    consumes uninitialized(p[0..n]);
    ensures result == p;
    produces allocation(result, n * 4);
    produces uninitialized(result[0..n]);
}

int32 caller(int32 n) {
    requires 1 <= n and n <= 1000;
    ensures result == 0 or result == 1;
}
```

`click verify` refuses `caller` at `q = touch(p, n)` with the population
message above. Dropping the two `uninitialized` clauses refuses the same way;
dropping `ensures result == p` verifies.

## Intended regression

The reproduction as an mdtest expecting `pass`, plus its refusal sibling with
`p[0] = 1;` after `free(q)` expecting a use-after-free refusal, and the
`size_t` variant (`size_t n`, `malloc(n * sizeof(uint32_t))`,
`allocation(p, n * 4u64)`, `requires 1u64 <= n and n <= 1000u64`) expecting
`pass`.

## Acceptance criteria

- The reproduction verifies, and so does its `size_t` variant.
- A use of `p` or `q` after `free(q)` is still refused.
- A callee that states `ensures result == p` but produces the allocation with
  a different byte count is still refused.
- No population-ledger message is reported for a program that uses no
  population resource.
