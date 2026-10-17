# Full pointer equalities compose through displaced C arguments

A C argument's address shares a block with other arguments. Rewriting its
complete value also rewrites that base inside a displaced copy. The symbolic
count case retains the address-association premise supplied by the checksum
proof's cursor lemma.

```c filename=compose.c
void compose(const unsigned char *base, const unsigned char *middle, const unsigned char *end) {}
void join(const unsigned char *base, const unsigned char *middle, const unsigned char *end, unsigned long first, unsigned long second) {}
```

```click
verifying "compose.c";
void compose(const uint8* base, const uint8* middle, const uint8* end) {
 requires middle == base + 2u64;
 requires end == middle + 3u64;
 ensures end == base + 5u64;
} by {
 execute();
 have base + 2u64 + 3u64 == base + 5u64 by normalize();
 simp() using {
  end == middle + 3u64;
  middle == base + 2u64;
  base + 2u64 + 3u64 == base + 5u64;
 };
}
void join(const uint8* base, const uint8* middle, const uint8* end, uint64 first, uint64 second) {
 requires first <= 100u64;
 requires second <= 100u64;
 requires middle == base + first;
 requires end == middle + second;
 requires base + first + second == base + (first + second);
 ensures end == base + (first + second);
} by {
 execute();
 simp() using {
  end == middle + second;
  middle == base + first;
  base + first + second == base + (first + second);
 };
}
```

```expect
pass
```
