# A retiring worker proves separation for the full allocation

The worker consumes only the allocation token. The launch must protect the
whole allocation even though the contract has no mutable element range.

```c filename=worker_retirement.c
#include <pthread.h>
#include <stddef.h>
void release(int *p);

void *retire(void *argument) {
    release(argument);
    return NULL;
}

int run(int *p, const unsigned char *q) {
    pthread_t handle;
    if (pthread_create(&handle, NULL, retire, p) != 0) {
        release(p);
        return 0;
    }
    pthread_join(handle, NULL);
    return 1;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "worker_retirement.c";

extern void release(int32 *p) {
    consumes allocation(p, 4);
}
void *retire(void *argument) {
    consumes allocation(argument as (int32 *), 4);
}
int32 run(int32 *p, const uint8 *q) {
    consumes allocation(p, 4);
    views q[0..1];
    requires separate(memory(((p as (void *)) as (uint8 *))[0..4]), memory(q[0..1]));
    ensures result == 0 or result == 1;
} by {
    step();
    have separate(memory(handle), memory(q[0..1])) by { known(); }
    step();
    branch {
        true => {
            step() by { known(); }
            step();
            solve();
        }
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
