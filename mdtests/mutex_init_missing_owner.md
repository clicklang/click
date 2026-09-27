# Mutex initialization: missing owner

This synthetic regression checks initialization's storage precondition.

```c filename=mutex_init_missing_owner.c
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
verifying "mutex_init_missing_owner.c";
int32 run(struct holder *holder) {
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
fail: missing resource fact
```
