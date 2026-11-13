# A return transport's source matches a held fact up to its binder's name

At a completed return outcome, the proof names `memset`'s historical
quantified postcondition with another binder and selects it by `assumption`.
It then preserves each read and its definedness explicitly using the separated
statement footprint.

```c filename=ms.c
#include <string.h>

void fill_t(unsigned char *dst) { memset(dst, 7, 4); dst[4] = 0; }
```

```click
import click::separation;
verifying "ms.c";

void fill_t(uint8* dst) {
    owns dst[0..5];
    ensures (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 });
} by {
    step_until(function.exit);
    have at(statement(1).entry,
        (0u64..4u64).all(|renamed| { defined(dst[renamed]) and dst[renamed] == 7 })) by {
        assumption();
    }
    have (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 }) by {
        intro(); intro();
        have separate(memory(dst[4u64]), memory(dst[k])) by {
            apply(separation::elements(dst, 4u64, k));
        }
        have separate(statement(1).footprint, memory(dst[k])) by {
            normalize() using { separate(memory(dst[4u64]), memory(dst[k])); };
        }
        have at(statement(1).exit, dst[k]) == at(statement(1).entry, dst[k]) by {
            preserve(separate(statement(1).footprint, memory(dst[k])));
        }
        instantiate(at(statement(1).entry,
            (0u64..4u64).all(|j| { defined(dst[j]) and dst[j] == 7 })), k) using { k < 4u64; };
        have defined(dst[k]) by {
            preserve(separate(statement(1).footprint, memory(dst[k])));
        }
        have dst[k] == 7u8 by { assumption(); }
        assumption();
    }
    assumption();
}
```

```expect
pass
```
