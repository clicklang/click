# Only the branch that sees a nonzero flag receives the payload

An acquire load that reads zero has not synchronized with the producer.
The branch that knows the value is zero keeps the subscriber right and
gets no payload.

```c filename=publication_unpublished_branch_does_not_receive.c
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
struct channel { atomic_int ready; int payload; };
int try_consume(struct channel *channel) {
    if (atomic_load_explicit(&channel->ready, memory_order_acquire) == 0) {
        return channel->payload;
    }
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "publication_unpublished_branch_does_not_receive.c";
resource ready_payload(channel: struct channel*) {
    owns channel->payload;
    fact channel->payload == 42;
}
int32 try_consume(struct channel* channel) {
    owns subscriber(&channel->ready, ready_payload(channel));
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `views channel->payload`
```
