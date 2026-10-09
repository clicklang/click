# A second release store has no publisher right

The publisher right is spent by the first release store. A second store
would publish a payload the producer no longer owns.

```c filename=publication_second_release_store_has_no_publisher.c
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
struct channel { atomic_int ready; int payload; };
void *producer(void *argument) {
    struct channel *channel = argument;
    channel->payload = 42;
    atomic_store_explicit(&channel->ready, 1, memory_order_release);
    atomic_store_explicit(&channel->ready, 2, memory_order_release);
    return NULL;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "publication_second_release_store_has_no_publisher.c";
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
    step();
    simp();
}
```

```expect
fail: a release store to a publication flag requires owns publisher(flag, P)
```
