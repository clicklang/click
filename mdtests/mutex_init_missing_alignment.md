# Mutex initialization: missing alignment

This synthetic regression checks initialization's storage precondition.

```c filename=mutex_init_missing_alignment.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
int run(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    pthread_mutex_destroy(&holder->mu);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_init_missing_alignment.c";
int32 run(struct holder *holder) {
    owns holder->mu;
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
fail: Requires aligned(&holder->mu, 8)
```
