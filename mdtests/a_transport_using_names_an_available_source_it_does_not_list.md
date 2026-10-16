# A `transport using` names an available source it does not list

Mid-execution, `transport using` reads only the facts its `using` list names,
so a source that is not listed is refused even though `memset`'s
postcondition holds it. The refusal says that: it names the source as an
available fact to list, rather than printing it as a missing fact beside the
available facts that hold it. Listing the source in `using` verifies.

```c filename=ms.c
#include <string.h>

void fill_t(unsigned char *dst) { memset(dst, 7, 4); dst[4] = 0; }
```

```click
verifying "ms.c";

void fill_t(uint8* dst) {
    owns dst[0..5];
    ensures (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 });
} by {
    step();
    step();
    have (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 }) by {
        transport(at(statement(1).entry, (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 })),
                  (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 })) using { };
    };
    execute();
}
```

```expect
fail: `transport using` requires a source derivable from its explicit facts: its source `at(statement(1).entry, (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 }))` is an available fact, but this check reads only the facts listed in `using`; list the source there
```
