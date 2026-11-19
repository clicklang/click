# A worker launch proves its write range separate from a live view

```c filename=worker_write.c
#include <pthread.h>
#include <stddef.h>

void *set_value(void *argument) {
    *(int *)argument = 7;
    return NULL;
}

int run(int *p, const int *q) {
    pthread_t handle;
    if (pthread_create(&handle, NULL, set_value, p) != 0)
        return 0;
    pthread_join(handle, NULL);
    return p[0];
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "worker_write.c";

void *set_value(void *argument) {
    owns (argument as (int32 *))[0..1];
    ensures (argument as (int32 *))[0] == 7;
}
int32 run(int32 *p, const int32 *q) {
    owns p[0..1];
    views q[0..1];
    requires separate(memory(p[0..1]), memory(q[0..1]));
    ensures result == 0 or result == 7;
} by {
    step();
    have separate(memory(handle), memory(q[0..1])) by { normalize(); }
    step();
    branch {
        true => { step(); solve(); }
        false => {}
    }
    step();
    step();
    solve();
}
```

```expect
pass
```
