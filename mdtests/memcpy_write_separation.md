# A memcpy destination is separate from an active borrow

The destination is already owned. The copy uses an entry separation fact
for its destination and the unrelated live borrow. A zero-byte copy beside
a view of the same object needs no separation proof.

```c filename=memcpy_write_separation.c
#include <string.h>

void copy_beside_view(unsigned char *dst, unsigned char *src, const unsigned char *q) {
    memcpy(dst, src, 4);
}

void empty_copy_beside_view(unsigned char *q, const unsigned char *src) {
    memcpy(q, src, 0);
}
```

```click
verifying "memcpy_write_separation.c";

void copy_beside_view(uint8* dst, uint8* src, const uint8* q) {
    owns dst[0..4];
    owns src[0..4];
    views q[0..1];
    requires separate(memory(dst[0u64..4u64]), memory(q[0..1]));
    ensures click::bytes::equal(dst, 0u64, src, 0u64, 4u64) by {
        have separate(memory(dst[0..4]), memory(src[0..4])) by { known(); }
        step() by { known(); }
        have separate(statement(0).footprint, memory(src[0..4])) by {
            solve() using { separate(memory(dst[0..4]), memory(src[0..4])); };
        }
        have contains(statement(0).footprint, statement(0).footprint) by {
            apply(click::separation::contains_refl(statement(0).footprint));
        }
        have contains(memory(src[0..4]), memory(src[0u64..4u64])) by { normalize(); }
        have forall (k: uint64) { k < 4u64 implies src[k] == old(src[k]) } by {
            intro();
            intro();
            have contains(memory(src[0u64..4u64]), memory(src[k])) by {
                apply(click::separation::contains_element(src, 0u64, 4u64, k));
            }
            have contains(memory(src[0..4]), memory(src[k])) by {
                apply(click::separation::contains_trans(memory(src[0..4]), memory(src[0u64..4u64]), memory(src[k])));
            }
            have separate(statement(0).footprint, memory(src[k])) by {
                apply(click::separation::separate_restrict(statement(0).footprint, memory(src[0..4]), statement(0).footprint, memory(src[k])));
            }
            have src[k] == at(statement(0).entry, src[k]) by {
                preserve(memory(src[k]), statement(0));
            }
            known();
        }
        step();
        unfold(click::bytes::equal(dst, 0u64, old(src), 0u64, 4u64));
        have click::bytes::equal(dst, 0u64, src, 0u64, 4u64) by {
            unfold(click::bytes::equal(dst, 0u64, src, 0u64, 4u64));
            intro();
            intro();
            instantiate(forall (k1: uint64) { true and k1 < 4u64 implies dst[0u64 + k1] == old(src[0u64 + k1]) }, k);
            instantiate(forall (k1: uint64) { k1 < 4u64 implies src[k1] == old(src[k1]) }, k);
            rewrite(src[k], old(src[k]));
            known();
        }
        known();
    }
}

void empty_copy_beside_view(uint8* q, const uint8* src) {
    owns q[0..1];
    views q[1..2];
    views src[0..1];
} by {
    step();
}
```

```expect
pass
```
