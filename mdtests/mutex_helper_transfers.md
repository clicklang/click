# Acquiring and releasing helpers use ordinary resource contracts

The wrappers return and consume the same guard and protected ownership as the
runtime operations. The nested wrappers exercise summary composition, and the
local proof names deliberately differ from the contract's output names.

```c filename=mutex_helper_transfers.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; unsigned int value; };

void acquire(struct counter *p) { pthread_mutex_lock(&p->mu); }
void release(struct counter *p) { pthread_mutex_unlock(&p->mu); }
void acquire_nested(struct counter *p) { acquire(p); }
void release_nested(struct counter *p) { release(p); }
void increment(struct counter *p) {
    acquire_nested(p);
    p->value = p->value + 1u;
    release_nested(p);
}
void run(struct counter *p) {
    pthread_mutex_init(&p->mu, 0);
    increment(p);
    pthread_mutex_destroy(&p->mu);
}
void run_direct(struct counter *p) {
    pthread_mutex_init(&p->mu, 0);
    acquire_nested(p);
    p->value = p->value + 1u;
    release_nested(p);
    pthread_mutex_destroy(&p->mu);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";

resource counter_state(p: struct counter*) {
    field value: uint32;
    owns p->value;
    fact p->value == value;
}

verifying "mutex_helper_transfers.c";

void acquire(struct counter *p) {
    owns access: mutex_use(&p->mu, counter_state(p));
    produces guard: mutex_guard(&p->mu);
    produces state: counter_state(p);
} by {
    let { guard: acquired, state: state } = step(pthread_mutex_lock(&p->mu), { access: access });
    step();
    simp();
}

void release(struct counter *p) {
    owns access: mutex_use(&p->mu, counter_state(p));
    consumes guard: mutex_guard(&p->mu);
    consumes state: counter_state(p);
} by {
    step(pthread_mutex_unlock(&p->mu), { access: access, guard: guard, state: state });
    step();
    simp();
}

void acquire_nested(struct counter *p) {
    owns permission: mutex_use(&p->mu, counter_state(p));
    produces locked: mutex_guard(&p->mu);
    produces contents: counter_state(p);
} by {
    let { guard: acquired, state: contents } = step(acquire(p), { access: permission });
    step();
    simp();
}

void release_nested(struct counter *p) {
    owns permission: mutex_use(&p->mu, counter_state(p));
    consumes locked: mutex_guard(&p->mu);
    consumes contents: counter_state(p);
} by {
    step(release(p), { access: permission, guard: locked, state: contents });
    step();
    simp();
}

void increment(struct counter *p) {
    owns access: mutex_use(&p->mu, counter_state(p));
} by {
    let { locked: acquired, contents: before } = step(acquire_nested(p), { permission: access });
    unfold(before);
    step();
    let restored = fold(counter_state(p), { value: p->value });
    step(release_nested(p), { permission: access, locked: acquired, contents: restored });
    step();
    simp();
}

void run(struct counter *p) {
    owns p->mu;
    requires aligned(&p->mu, 8);
    owns initial: counter_state(p);
} by {
    let { lifetime: lifetime } = step(pthread_mutex_init(&p->mu, 0), { state: initial });
    step(increment(p), { access: lifetime });
    step(pthread_mutex_destroy(&p->mu), { lifetime: lifetime });
    step();
    simp();
}

void run_direct(struct counter *p) {
    owns p->mu;
    requires aligned(&p->mu, 8);
    consumes initial: counter_state(p);
    produces restored: counter_state(p);
} by {
    let { lifetime: lifetime } = step(pthread_mutex_init(&p->mu, 0), { state: initial });
    let { locked: acquired, contents: before } = step(acquire_nested(p), { permission: lifetime });
    unfold(before);
    step();
    let restored = fold(counter_state(p), { value: p->value });
    step(release_nested(p), { permission: lifetime, locked: acquired, contents: restored });
    step(pthread_mutex_destroy(&p->mu), { lifetime: lifetime });
    step();
    simp();
}
```

```expect
pass
```
