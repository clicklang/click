# Mutex protects memory; workers own separate contribution units

The C is copied unchanged from `design/concurrency-probes/mutex_counter.c`.
The ordinary protected resource owns memory directly. Workers hold separate
abstract contribution units, so their units cannot expose the protected body.
Both workers can run, consume one unit each, and join through the existing
protocol. The proof checks totals before cleanup on each failure/success path.

This is a composition control, not the exact-two proof. The parent receives
two units in its contract; it does not initialize them from memory. Its
`consumes` clause also spends any unused units on failure at function return.
The intermediate Count checks distinguish completed work from that cleanup.
There is no invariant linking contribution consumption to the counter value.

```c filename=mutex_counter.c
#include <pthread.h>
#include <stddef.h>

struct mutex_counter {
    pthread_mutex_t mutex;
    unsigned int value;
};

void *increment_counter(void *argument) {
    struct mutex_counter *counter = argument;
    (void)pthread_mutex_lock(&counter->mutex);
    counter->value = counter->value + 1u;
    (void)pthread_mutex_unlock(&counter->mutex);
    return NULL;
}

int increment_twice(struct mutex_counter *counter) {
    pthread_t first;
    pthread_t second;

    counter->value = 0u;
    if (pthread_mutex_init(&counter->mutex, NULL) != 0) return 0;
    if (pthread_create(&first, NULL, increment_counter, counter) != 0) {
        (void)pthread_mutex_destroy(&counter->mutex);
        return 0;
    }
    if (pthread_create(&second, NULL, increment_counter, counter) != 0) {
        (void)pthread_join(first, NULL);
        (void)pthread_mutex_destroy(&counter->mutex);
        return 0;
    }

    (void)pthread_join(first, NULL);
    (void)pthread_join(second, NULL);
    (void)pthread_mutex_destroy(&counter->mutex);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_counter.c";

abstract resource contribution(counter: struct mutex_counter*);

resource counter_state(counter: struct mutex_counter*) {
    field value: uint32;
    guarded_by counter->mutex;
    owns counter->value;
    fact counter->value == value;
}

void* increment_counter(void* argument) {
    consumes contribution((struct mutex_counter*)argument);
    owns access: mutex_use(
        &((struct mutex_counter*)argument)->mutex,
        counter_state((struct mutex_counter*)argument)
    );
    ensures result == 0;
} by {
    step();
    step();
    let { guard: guard, state: state } = step(
        pthread_mutex_lock(&counter->mutex), { access: access }
    );
    unfold(state);
    step();
    let restored = fold(counter_state(counter), { value: counter->value });
    step(pthread_mutex_unlock(&counter->mutex), {
        access: access, guard: guard, state: restored
    });
    step();
    simp();
}

int32 increment_twice(struct mutex_counter* counter) {
    consumes 2 of contribution(counter);
    requires count(contribution(counter)) == 2;
    owns &counter->mutex;
    requires aligned(&counter->mutex, 8);
    owns counter->value;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    step();
    let state = fold(counter_state(counter), { value: counter->value });
    let { lifetime: lifetime } = step(pthread_mutex_init(&counter->mutex, 0), { state: state });
    branch then { have count(contribution(counter)) == 2 by { simp(); } unfold(state); step(); simp(); } else {}
    step();
    branch then {
        have count(contribution(counter)) == 2 by { simp(); }
        step(pthread_mutex_destroy(&counter->mutex), { lifetime: lifetime });
        unfold(state);
        step();
        simp();
    } else {}
    step();
    branch then {
        step();
        have count(contribution(counter)) == 1 by { simp(); }
        step(pthread_mutex_destroy(&counter->mutex), { lifetime: lifetime });
        unfold(state);
        step();
        simp();
    } else {}
    step();
    step();
    have count(contribution(counter)) == 0 by { simp(); }
    step(pthread_mutex_destroy(&counter->mutex), { lifetime: lifetime });
    unfold(state);
    step();
    simp();
}
```

```expect
pass
```
