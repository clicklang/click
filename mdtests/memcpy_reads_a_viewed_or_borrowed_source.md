# memcpy reads a viewed or borrowed source

The standard-library `memcpy` contract owns its destination and views its
source. A caller that only views the source lends that view to the call
(`copy_viewed`). A caller that owns the source lends it as a view for the
call and gets its ownership back afterwards, so it can write the source
again (`copy_then_clear`). Both keep `memcpy`'s byte-equality postcondition.
Overlapping ranges are refused
([`byte_representation_overlapping_copy_rejected.md`](byte_representation_overlapping_copy_rejected.md)).

```c filename=memcpy_reads_a_viewed_or_borrowed_source.c
#include <string.h>
void copy_viewed(unsigned char *dst, const unsigned char *src) {
    memcpy(dst, src, 4);
}
void copy_then_clear(unsigned char *dst, unsigned char *src) {
    memcpy(dst, src, 4);
    src[0] = 0;
}
```

```click
verifying "memcpy_reads_a_viewed_or_borrowed_source.c";
void copy_viewed(uint8* dst, const uint8* src) {
    views src[0..4];
    owns dst[0..4];
    ensures click::bytes::equal(dst, 0u64, src, 0u64, 4u64) by {
        step();
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
                apply(click::separation::contains_element(src, 0u64, 4u64, k)) using { 0u64 <= k; k < 4u64; };
            }
            have contains(memory(src[0..4]), memory(src[k])) by {
                apply(click::separation::contains_trans(memory(src[0..4]), memory(src[0u64..4u64]), memory(src[k]))) using {
                    contains(memory(src[0..4]), memory(src[0u64..4u64]));
                    contains(memory(src[0u64..4u64]), memory(src[k]));
                };
            }
            have separate(statement(0).footprint, memory(src[k])) by {
                apply(click::separation::separate_restrict(statement(0).footprint, memory(src[0..4]), statement(0).footprint, memory(src[k]))) using {
                    separate(statement(0).footprint, memory(src[0..4]));
                    contains(statement(0).footprint, statement(0).footprint);
                    contains(memory(src[0..4]), memory(src[k]));
                };
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

void copy_then_clear(uint8* dst, uint8* src) {
    owns src[0..4];
    owns dst[0..4];
    ensures src[0] == 0;
}
```

```expect
pass
```
