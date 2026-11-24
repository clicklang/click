# Copied bytes survive the terminator store after `memcpy`

After `memcpy`, writing the terminator at `dst[n]` leaves every copied
byte `dst[k]` with `k < n` unchanged. The source byte is separate from
the write footprints of both the call and the store. The proof preserves
those reads individually and instantiates `memcpy`'s postcondition at the
chosen index. Casting the `char *` arguments to `uint8 *` names the same
byte reads as the unfolded postcondition.

```c filename=copy.c
#include <string.h>
void copy_n(char *dst, const char *src, unsigned long n) { memcpy(dst, src, n); dst[n] = '\0'; }
```

```click
import click::bytes;
import click::separation;
verifying "copy.c";
void copy_n(char* dst, const char* src, uint64 n) {
    views src[0u64..n];
    owns dst[0u64..n + 1u64];
    requires n < 32u64;
    requires separate(memory(dst[0u64..n + 1u64]), memory(src[0u64..n]));
    ensures bytes::equal(dst, 0u64, src, 0u64, n);
} by {
    unfold(bytes::equal(dst, 0u64, src, 0u64, n));
    step();
    mark copied;
    step();
    have bytes::equal(dst, 0u64, src, 0u64, n) by {
        unfold(bytes::equal(dst, 0u64, src, 0u64, n));
        intro(); intro();
        have separate(memory((dst as (uint8 *))[n]), memory((dst as (uint8 *))[k])) by {
            apply(separation::separate_elements(dst as (uint8 *), n, k));
        }
        have separate(statement(1).footprint, memory((dst as (uint8 *))[k])) by {
            close() using { separate(memory((dst as (uint8 *))[n]), memory((dst as (uint8 *))[k])); };
        }
        have (dst as (uint8 *))[k] == at(copied, (dst as (uint8 *))[k]) by {
            preserve(memory((dst as (uint8 *))[k]), statement(1));
        }
        instantiate(at(copied, (0u64..n).all(|j| {
            (dst as (uint8 *))[0u64 + j] == old((src as (uint8 *))[0u64 + j])
        })), k);
        apply(separation::contains_element(src as (uint8 *), 0u64, n, k));
        have contains(memory(dst[0u64..n]), statement(0).footprint) by { close(); }
        apply(separation::separate_restrict(
            memory(dst[0u64..n]), memory(src[0u64..n]),
            statement(0).footprint, memory((src as (uint8 *))[k])
        ));
        have at(copied, (src as (uint8 *))[k]) == old((src as (uint8 *))[k]) by {
            preserve(memory((src as (uint8 *))[k]), statement(0));
        }
        apply(separation::contains_refl(memory((dst as (uint8 *))[n])));
        apply(separation::separate_restrict(
            memory((dst as (uint8 *))[n]), memory(src[0u64..n]),
            memory((dst as (uint8 *))[n]), memory((src as (uint8 *))[k])
        ));
        have separate(statement(1).footprint, memory((src as (uint8 *))[k])) by {
            close() using { separate(memory((dst as (uint8 *))[n]), memory((src as (uint8 *))[k])); };
        }
        have (src as (uint8 *))[k] == at(copied, (src as (uint8 *))[k]) by {
            preserve(memory((src as (uint8 *))[k]), statement(1));
        }
        rewrite((src as (uint8 *))[k], at(copied, (src as (uint8 *))[k]));
        rewrite(at(copied, (src as (uint8 *))[k]), old((src as (uint8 *))[k]));
        rewrite((dst as (uint8 *))[k], at(copied, (dst as (uint8 *))[k]));
        close();
    }
}
```

```expect
pass
```
