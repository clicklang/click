# A resource fact's unsigned quantifier guard needs a redundant `0 <= k`

Soundness: incomplete. The check refuses a well-covered resource definition;
it never accepts an uncovered read.

A composite resource's quantified `fact` that reads `bytes[k]` under the guard
`k < len`, with `k: uint64` and a contained `views bytes[0u64..len]`, is
refused as reading without a covering resource. The diagnostic says the
available facts do not prove `0u64 <= k < len` and that no scalar assumptions
were available, although `k < len` is the guard and `0u64 <= k` holds for
every `uint64`. Adding the redundant `0u64 <= k and` to the guard makes the
same definition check; `click::cstr::cstr_at` writes it that way. Signed
binders state the lower bound anyway, which is why most of the corpus never
meets this.

## Reproduction

```c filename=probe.c
uint8 first(uint8 bytes[], uint64 len) { return bytes[0]; }
```

```click
verifying "probe.c";
resource prefix(bytes: uint8*, len: uint64) {
    views bytes[0u64..len];
    fact forall (k: uint64) { k < len implies bytes[k] != '\0' };
}
uint8 first(uint8 bytes[], uint64 len) {
    requires 0u64 < len;
    views prefix(bytes, len);
    ensures true;
} by { execute(); simp(); }
```

Observed on 2026-10-16 on master `40d34180` plus the M3 `memcpy`/`memcmp` contract change, which does not touch this path: `resource `prefix` fact reads
`bytes[k]` without a covering contained memory resource with current read
authority`, noting "the available scalar facts do not prove `0u64` <= `k` <
`len`" and "no scalar fact assumptions were available". With
`{ 0u64 <= k and k < len implies ... }` it verifies.

## Acceptance

- The reproduction verifies as written, kept as an mdtest.
- The coverage check takes an unsigned binder's lower bound from its type and
  uses a lone `k < len` guard; a guard that does not bound `k` below the
  range end is still refused.
- No per-fact scan of unrelated facts is added to the check.
