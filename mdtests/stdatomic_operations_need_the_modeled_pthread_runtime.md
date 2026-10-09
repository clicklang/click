# C11 atomic operations need the modeled-pthread runtime

Click's `<stdatomic.h>` projection declares the atomic operations for every
user-space target, but only the modeled-pthread runtime gives them meaning.
Without it, a proof that reaches one is refused by name rather than as an
undefined function.

```c filename=stdatomic_operations_need_the_modeled_pthread_runtime.c
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
verifying "stdatomic_operations_need_the_modeled_pthread_runtime.c";
void publish(struct channel *channel) {
    owns channel->payload;
    owns channel->ready;
} by { execute(); simp(); }
```

```expect
fail: `atomic_store_explicit` is declared by Click's `<stdatomic.h>` projection, but only the modeled-pthread thread runtime models C11 atomic operations
```
