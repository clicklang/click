# Mutex payloads preserve an ordinary symbolic token quantity

The unchanged worker can unfold and restore a variable-size ordinary token bundle. Token quantities contribute no memory footprint.

```c filename=mutex_use_preserves_resource_quantity.c
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
verifying "mutex_use_preserves_resource_quantity.c";
abstract resource increment_credit(counter: struct mutex_counter*);
resource counter_state(counter: struct mutex_counter*) {
    field value: uint32;
    field credits: int32;
    owns counter->value;
    owns credits of increment_credit(counter);
    fact credits >= 0;
    fact credits <= 2;
    fact counter->value == value;
}
void* increment_counter(void* argument) {
    owns access: mutex_use(&((struct mutex_counter*)argument)->mutex, counter_state((struct mutex_counter*)argument));
    ensures result == 0;
} by {
    step();
    step();
    let { guard: guard, state: state } = step(pthread_mutex_lock(&counter->mutex), { access: access });
    let { credits: n } = unfold(state);
    step();
    let restored = fold(counter_state(counter), { value: counter->value, credits: n });
    step(pthread_mutex_unlock(&counter->mutex), { access: access, guard: guard, state: restored });
    step();
    simp();
}
```

```expect
pass
```
