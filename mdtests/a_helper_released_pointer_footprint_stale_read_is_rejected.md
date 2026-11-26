# A helper-released pointer footprint is forgotten at the call

The protected state owns a pointer cell and the memory it points to, a
footprint that depends on memory (a helper's protected state is a leaf
resource, so it reaches the memory directly rather than through a child). The worker locks and unlocks through acquiring and
releasing helpers, and reads that memory in two critical sections. Another
thread may store between them, so the second read is not the first.

The releasing helper's protocol step is part of its call: the call forgets
the footprint the worker released, found through the pointer value it held
at the call's entry, which the callee's effects leave in place.

```c filename=helper_pointer_footprint.c
#include <pthread.h>
struct box { pthread_mutex_t mu; int *slot; };
void acquire(struct box *b) { pthread_mutex_lock(&b->mu); }
void release(struct box *b) { pthread_mutex_unlock(&b->mu); }
int read_twice(struct box *b) {
    int first;
    int second;
    acquire(b);
    first = *b->slot;
    release(b);
    acquire(b);
    second = *b->slot;
    release(b);
    return first == second;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "helper_pointer_footprint.c";
resource box_state(b: struct box*) {
    field v: int32;
    owns b->slot;
    owns *b->slot;
    fact *b->slot == v;
}

void acquire(struct box *b) {
    owns access: mutex_use(&b->mu, box_state(b));
    produces guard: mutex_guard(&b->mu);
    produces state: box_state(b);
} by {
    let { guard: acquired, state: state } = step(pthread_mutex_lock, { access: access });
    step();
    close();
}

void release(struct box *b) {
    owns access: mutex_use(&b->mu, box_state(b));
    consumes guard: mutex_guard(&b->mu);
    consumes state: box_state(b);
} by {
    step(pthread_mutex_unlock, { access: access, guard: guard, state: state });
    step();
    close();
}

int32 read_twice(struct box *b) {
    owns access: mutex_use(&b->mu, box_state(b));
    ensures result == 1;
} by {
    step();
    step();
    let { guard: first_guard, state: first_state } = step(acquire, { access: access });
    let { v: first_v } = unfold(first_state);
    step();
    let first_restored = fold(box_state(b), { v: *b->slot });
    step(release, { access: access, guard: first_guard, state: first_restored });
    let { guard: second_guard, state: second_state } = step(acquire, { access: access });
    let { v: second_v } = unfold(second_state);
    step();
    let second_restored = fold(box_state(b), { v: *b->slot });
    step(release, { access: access, guard: second_guard, state: second_restored });
    step();
    close();
}
```

```expect
fail: `ensures result == 1` failed
```
