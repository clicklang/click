# A false bounded universal over uint64 is refused

`k < 3u64` has the members 0, 1 and 2, and the last does not satisfy
`k <= 1u64`. The enumeration checks every member, so the claim is refused.

`a_bounded_universal_over_uint64_is_enumerated.md` has the claims that
hold.

```c filename=a_false_bounded_universal_over_uint64_is_refused.c
void nop(unsigned long length) { }
```

```click
verifying "a_false_bounded_universal_over_uint64_is_refused.c";

void nop(uint64 length) {
    ensures forall (k: uint64) { k < 3u64 implies k <= 1u64 };
} by { execute(); simp(); }
```

```expect
fail: unclosed goal
```
