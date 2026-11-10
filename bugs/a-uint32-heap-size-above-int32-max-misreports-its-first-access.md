# A `uint32` heap size above `INT32_MAX` misreports its first access as UB

Soundness: soundness-adjacent. No false claim is known to verify: with the
default proof a false postcondition in the success branch (malloc, then
free, then `return 2`) is still refused. But the kernel admits a heap block
whose recorded extent is ill-formed (a `uint32` term stored in the `int32`
token slot and range bound, where it reads as a negative count), and the
resulting verdict is wrong: a valid access is reported as undefined behavior.

The heap extent is a checked signed 32-bit value
([`design/heap-extents.md`](../design/heap-extents.md)).
`allocation_size_value` (`src/kernel/eval/statements.rs`) admits a symbolic
`UInt32` size as unsigned and decides only positivity (raw path) or
`n <= u32::MAX / w` (element path). It then stores the term unchanged in
`allocation(p, int32(n))` and `p[Int32:0..n]`. For `n >= 2^31` the signed
reading is negative, so the first valid access fails pointer formation. The
same admission is repeated in `execute_c_realloc_assign_paths`.

## Reproduction

```c
#include <stdlib.h>
#include <stdint.h>

int big(uint32_t n) {
    uint8_t *p = malloc(n);
    if (p == 0) {
        return 0;
    }
    p[0] = 1;
    int r = p[0];
    free(p);
    return r;
}
```

```click
verifying "big.c";

int32 big(uint32 n) {
    requires n == 3000000000u32;
    ensures result == 0 or result == 1;
}
```

Observed: "`step()` produced undefined behavior: pointer arithmetic left the
pointed-to object", at `p[0] = 1;`, with resources
`owns allocation(ptr<int32*>(p), int32(n)); owns memory(p[Int32:0..n], stride=1)`.
The same happens for `n == 2147483648u32` and for `1u32 <= n and n <= 3000000000u32`.
`n == 2147483647u32` verifies.

## Acceptance

- `malloc` (and `realloc`) of a `uint32` size not known to be at most
  `INT32_MAX` bytes, or an element count not known to be at most
  `INT32_MAX / w`, is refused at the allocation statement with a message
  naming the 32-bit extent bound.
- An mdtest keeps this source pattern and expects that refusal; a `uint32`
  size bounded by `INT32_MAX` still verifies.
