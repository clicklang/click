# A held mutex keeps its allocation live

The allocator comes from Click's built-in `<stdlib.h>` and the mutex from its
built-in `<pthread.h>`.


```c filename=mutex_storage_free_held.c
#include <pthread.h>
#include <stdlib.h>
struct holder { int prefix; pthread_mutex_t mu; };
int run(void) {
    struct holder *holder = malloc(sizeof(struct holder));
    if (holder == 0) return 0;
    pthread_mutex_init(&holder->mu, 0);
    pthread_mutex_lock(&holder->mu);
    free(holder);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_storage_free_held.c";
int32 run() {
    ensures result == 0 by auto;
}
```

```expect
fail: Cannot release allocation
```
