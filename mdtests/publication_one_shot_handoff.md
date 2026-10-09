# One-shot release/acquire publication hands the payload to one reader

The producer writes the payload, then publishes it with a release store. The
consumer spins on an acquire load; the branch that sees a nonzero flag
receives `ready_payload(channel)` and reads the value the producer wrote.
`atomic_init` mints the two rights and takes the flag storage, which stays
taken because C has no atomic destroy.

```c filename=publication_one_shot_handoff.c
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>

struct channel {
    atomic_int ready;
    int payload;
};

void *producer(void *argument) {
    struct channel *channel = argument;
    channel->payload = 42;
    atomic_store_explicit(&channel->ready, 1, memory_order_release);
    return NULL;
}

int consume(struct channel *channel) {
    while (atomic_load_explicit(&channel->ready, memory_order_acquire) == 0) {
    }
    return channel->payload;
}

int publish_once(struct channel *channel) {
    pthread_t thread;
    int value;

    atomic_init(&channel->ready, 0);
    if (pthread_create(&thread, NULL, producer, channel) != 0) return -1;
    value = consume(channel);
    (void)pthread_join(thread, NULL);
    return value;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "publication_one_shot_handoff.c";

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
    ensures result == 0;
} by {
    step();
    step();
    step();
    fold(ready_payload(channel));
    step();
    step();
    simp();
}

int32 consume(struct channel* channel) diverges {
    consumes subscriber(&channel->ready, ready_payload(channel));
    produces ready_payload(channel);
    ensures result == 42;
} by {
    loop diverges {
        owns subscriber(&channel->ready, ready_payload(channel));
    }
    unfold(ready_payload(channel));
    step();
    fold(ready_payload(channel));
    simp();
}

int32 publish_once(struct channel* channel) diverges {
    consumes channel->ready;
    owns channel->payload;
    requires aligned(&channel->ready, 4);
    ensures result == 42 or result == -1;
} by {
    step();
    step();
    step(atomic_init(&channel->ready, 0), { payload: ready_payload(channel) });
    step();
    branch then {
        step();
        simp();
    } else {}
    step();
    step();
    unfold(ready_payload(channel));
    step();
    simp();
}
```

```expect
pass
```
