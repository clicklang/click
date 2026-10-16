# Numeric address gaps preserve complete words

Two adjacent eight-byte cells retain their values across a store, even when
only their numeric addresses connect their pointer spellings.

```c filename=numeric_address_gap_preserves_word.c
#include <stdint.h>
uint64_t keep(uint64_t *p, uint64_t *q) { *q = 9; return *p; }
```

```click
verifying "numeric_address_gap_preserves_word.c";
uint64 keep(uint64* p, uint64* q) {
    owns *p;
    owns *q;
    requires address(q) == address(p + 1);
    requires *p == 17;
    ensures result == 17;
} by {
    step();
    have separate(memory(*p), memory(*q)) by { assumption(); }
    have *p == 17 by { assumption(); }
    execute(); simp();
}
```

```expect
pass
```
