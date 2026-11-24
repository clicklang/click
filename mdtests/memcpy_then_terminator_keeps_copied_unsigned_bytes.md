# Copied `unsigned char` bytes survive the terminator store

The copy uses a `uint64` index to read the `uint8` bytes, while the
contract uses 32-bit range bounds. The guard `k < 4u64` makes the source
byte available within `src[0..4]` and distinguishes the destination byte
from the terminator at `dst[4]`.

Both proofs name the preserved reads across the call and store and
instantiate the saved `memcpy` postcondition. `copy_u` composes the
equalities with rewrites. `copy_u_smart` supplies the same byte facts to
`close()` for the final equality.

```c filename=copy.c
#include <string.h>
void copy_u(unsigned char *dst, const unsigned char *src) { memcpy(dst, src, 4); dst[4] = 0; }
void copy_u_smart(unsigned char *dst, const unsigned char *src) { memcpy(dst, src, 4); dst[4] = 0; }
```

```click
import click::bytes;
import click::separation;
verifying "copy.c";
void copy_u(uint8* dst, const uint8* src) {
    views src[0..4];
    owns dst[0..5];
    requires separate(memory(dst[0..5]), memory(src[0..4]));
    ensures bytes::equal(dst, 0u64, src, 0u64, 4u64);
} by {
    unfold(bytes::equal(dst, 0u64, src, 0u64, 4u64));
    step();
    mark copied;
    step();
    have bytes::equal(dst, 0u64, src, 0u64, 4u64) by {
        unfold(bytes::equal(dst, 0u64, src, 0u64, 4u64));
        intro(); intro();
        have separate(memory(dst[4u64]), memory(dst[k])) by {
            apply(separation::separate_elements(dst, 4u64, k));
        }
        have separate(statement(1).footprint, memory(dst[k])) by {
            close() using { separate(memory(dst[4u64]), memory(dst[k])); };
        }
        have dst[k] == at(copied, dst[k]) by {
            preserve(memory(dst[k]), statement(1));
        }
        instantiate(at(copied, (0u64..4u64).all(|j| {
            dst[0u64 + j] == old(src[0u64 + j])
        })), k);
        have separate(memory(dst[0..4]), memory(src[k])) by { close(); }
        have contains(memory(dst[0..4]), statement(0).footprint) by { close(); }
        apply(separation::contains_refl(memory(src[k])));
        apply(separation::separate_restrict(
            memory(dst[0..4]), memory(src[k]),
            statement(0).footprint, memory(src[k])
        ));
        have at(copied, src[k]) == old(src[k]) by {
            preserve(memory(src[k]), statement(0));
        }
        have separate(memory(dst[4u64]), memory(src[k])) by { close(); }
        have separate(statement(1).footprint, memory(src[k])) by {
            close() using { separate(memory(dst[4u64]), memory(src[k])); };
        }
        have src[k] == at(copied, src[k]) by {
            preserve(memory(src[k]), statement(1));
        }
        rewrite(src[k], at(copied, src[k]));
        rewrite(at(copied, src[k]), old(src[k]));
        rewrite(dst[k], at(copied, dst[k]));
        close();
    }
}
void copy_u_smart(uint8* dst, const uint8* src) {
    views src[0..4];
    owns dst[0..5];
    requires separate(memory(dst[0..5]), memory(src[0..4]));
    ensures bytes::equal(dst, 0u64, src, 0u64, 4u64);
} by {
    unfold(bytes::equal(dst, 0u64, src, 0u64, 4u64));
    step();
    mark copied;
    step();
    have bytes::equal(dst, 0u64, src, 0u64, 4u64) by {
        unfold(bytes::equal(dst, 0u64, src, 0u64, 4u64));
        intro(); intro();
        have separate(memory(dst[4u64]), memory(dst[k])) by {
            apply(separation::separate_elements(dst, 4u64, k));
        }
        have separate(statement(1).footprint, memory(dst[k])) by {
            close() using { separate(memory(dst[4u64]), memory(dst[k])); };
        }
        have dst[k] == at(copied, dst[k]) by {
            preserve(memory(dst[k]), statement(1));
        }
        instantiate(at(copied, (0u64..4u64).all(|j| {
            dst[0u64 + j] == old(src[0u64 + j])
        })), k);
        have separate(memory(dst[0..4]), memory(src[k])) by { close(); }
        have contains(memory(dst[0..4]), statement(0).footprint) by { close(); }
        apply(separation::contains_refl(memory(src[k])));
        apply(separation::separate_restrict(
            memory(dst[0..4]), memory(src[k]),
            statement(0).footprint, memory(src[k])
        ));
        have at(copied, src[k]) == old(src[k]) by {
            preserve(memory(src[k]), statement(0));
        }
        have separate(memory(dst[4u64]), memory(src[k])) by { close(); }
        have separate(statement(1).footprint, memory(src[k])) by {
            close() using { separate(memory(dst[4u64]), memory(src[k])); };
        }
        have src[k] == at(copied, src[k]) by {
            preserve(memory(src[k]), statement(1));
        }
        close();
    }
}

```

```expect
pass
```
