# A publishing store must store a nonzero value

Zero means "not yet published" to the acquiring side, so storing zero
would hand over the payload without any reader being able to tell.

```c filename=publication_store_must_publish_a_nonzero_value.c
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
struct channel { atomic_int ready; int payload; };
void *producer(void *argument) {
    struct channel *channel = argument;
    channel->payload = 42;
    atomic_store_explicit(&channel->ready, 0, memory_order_release);
    return NULL;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "publication_store_must_publish_a_nonzero_value.c";
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
fail: a publishing store must store a value proven nonzero
```
