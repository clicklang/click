# An acquire load whose value is never tested receives nothing

The payload arrives with the knowledge that the loaded value is nonzero.
A load whose value no C branch tests leaves the subscriber right undecided,
so the payload stays unavailable.

```c filename=publication_untested_acquire_does_not_receive.c
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
struct channel { atomic_int ready; int payload; };
int consume_blindly(struct channel *channel) {
    (void)atomic_load_explicit(&channel->ready, memory_order_acquire);
    return channel->payload;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "publication_untested_acquire_does_not_receive.c";
resource ready_payload(channel: struct channel*) {
    owns channel->payload;
    fact channel->payload == 42;
}
int32 consume_blindly(struct channel* channel) {
    owns subscriber(&channel->ready, ready_payload(channel));
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `views channel->payload`
```
