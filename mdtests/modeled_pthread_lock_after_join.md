# A parent locks its own mutex after joining a typed `mutex_use` worker

After `pthread_join` the worker's use of the mutex is over and the parent holds
the lifecycle authority again, so a plain lock, unlock, and destroy by the parent
are accepted exactly as before the create. The join must not leave the worker's
preserved `mutex_use` in the parent's frame beside the restored `mutex_live`.

```c filename=modeled_pthread_lock_after_join.c
#include <pthread.h>
#include <stddef.h>
struct counter { pthread_mutex_t mu; unsigned int value; };
void *worker(void *argument) {
    struct counter *counter = argument;
    pthread_mutex_lock(&counter->mu);
    counter->value = counter->value + 1u;
    pthread_mutex_unlock(&counter->mu);
    return NULL;
}
unsigned int run(struct counter *counter) {
    pthread_t thread;
    pthread_mutex_init(&counter->mu, NULL);
    if (pthread_create(&thread, NULL, worker, counter) != 0) {
        pthread_mutex_destroy(&counter->mu);
        return 0u;
    }
    pthread_join(thread, NULL);
    pthread_mutex_lock(&counter->mu);
    pthread_mutex_unlock(&counter->mu);
    pthread_mutex_destroy(&counter->mu);
    return 1u;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_lock_after_join.c";
resource counter_state(counter: struct counter*) {
    field value: uint32;
    owns counter->value;
    fact counter->value == value;
}
void* worker(void* argument) {
    owns access: mutex_use(&((struct counter*)argument)->mu, counter_state((struct counter*)argument));
    ensures result == 0;
} by {
    step();
    step();
    let { guard: guard, state: state } = step(pthread_mutex_lock(&counter->mu), { access: access });
    unfold(state);
    step();
    let restored = fold(counter_state(counter), { value: counter->value });
    step(pthread_mutex_unlock(&counter->mu), { access: access, guard: guard, state: restored });
    step();
    simp();
}
uint32 run(struct counter* counter) {
    owns counter->mu;
    requires aligned(&counter->mu, 8);
    owns initial: counter_state(counter);
    ensures result == 0 or result == 1;
} by {
    step();
    let { lifetime: lifetime } = step(pthread_mutex_init(&counter->mu, 0), { state: initial });
    step();
    branch then {
        step(pthread_mutex_destroy(&counter->mu), { lifetime: lifetime });
        step();
        simp();
    } else {}
    step();
    step();
    step();
    step(pthread_mutex_destroy(&counter->mu), { lifetime: lifetime });
    step();
    simp();
}
```

```expect
pass
```
