# C11 atomic operations are declared but not modeled yet

Click's `<stdatomic.h>` projection lets the publication example parse
unchanged. No runtime models the atomic operations yet, so a proof that
reaches one is refused by name rather than as an undefined function.

```c filename=stdatomic_operations_are_not_modeled_yet.c
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
struct channel { atomic_int ready; int payload; };
void publish(struct channel *channel) {
    channel->payload = 42;
    atomic_store_explicit(&channel->ready, 1, memory_order_release);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "stdatomic_operations_are_not_modeled_yet.c";
void publish(struct channel *channel) {
    owns channel->payload;
    owns channel->ready;
} by { execute(); simp(); }
```

```expect
fail: `atomic_store_explicit` is declared by Click's `<stdatomic.h>` projection, but no runtime models C11 atomic operations yet
```
