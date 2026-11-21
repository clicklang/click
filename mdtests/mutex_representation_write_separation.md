# A mutex representation write can proceed beside a live view

```c filename=mutex_representation_write.c
#include <pthread.h>
#include <stddef.h>

struct holder { pthread_mutex_t mutex; };

int run(const int *q) {
    struct holder holder;
    pthread_mutex_init(&holder.mutex, NULL);
    pthread_mutex_lock(&holder.mutex);
    pthread_mutex_unlock(&holder.mutex);
    pthread_mutex_destroy(&holder.mutex);
    return q[0];
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "mutex_representation_write.c";

int32 run(const int32 *q) {
    views q[0..1];
    ensures result == q[0];
} by {
    step();
    have separate(memory(((&holder.mutex) as (uint8 *))[0..40]), memory(q[0..1])) by {
        known();
    }
    step();
    step();
    step();
    step();
    step();
}
```

```expect
pass
```
