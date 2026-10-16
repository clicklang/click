# An unsigned binder's guard needs no redundant lower bound

A composite resource's quantified `fact` reads `bytes[k]` under the guard
`k < len`. The binder is a `uint64`, so its type bounds it below by `0u64`,
and the contained `views bytes[0u64..len]` covers every read the guard admits.
`resource_fact_unsigned_guard_needs_upper_bound.md` keeps refusing a guard
that does not bound `k` below the range end.

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

```expect
pass
```
