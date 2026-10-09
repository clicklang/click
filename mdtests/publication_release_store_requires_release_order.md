# A publishing store must use release order

A relaxed store does not order the payload write before the flag, so a
reader that sees the flag could still read a stale payload. Only
`memory_order_release` publishes.

```c filename=publication_release_store_requires_release_order.c
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
struct channel { atomic_int ready; int payload; };
void *producer(void *argument) {
    struct channel *channel = argument;
    channel->payload = 42;
    atomic_store_explicit(&channel->ready, 1, memory_order_relaxed);
    return NULL;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "publication_release_store_requires_release_order.c";
resource ready_payload(channel: struct channel*) {
    owns channel->payload;
    fact channel->payload == 42;
}
void* producer(void* argument) {
    consumes publisher(
        &((struct channel*)argument)->ready,
        ready_payload((struct channel*)argument)
    );
    consumes ((struct channel*)argument)->payload;
} by {
    step();
    step();
    step();
    fold(ready_payload(channel));
    step();
    step();
    simp();
}
```

```expect
fail: atomic_store_explicit with memory_order_relaxed is not supported; one-shot publication uses memory_order_release
```
