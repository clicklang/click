# Mutex initialization: view only

This synthetic regression checks initialization's storage precondition.

```c filename=mutex_init_view_only.c
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
verifying "mutex_init_view_only.c";
int32 run(struct holder *holder) {
    views holder->mu;
    requires aligned(&holder->mu, 8);
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
fail: missing resource fact
```
