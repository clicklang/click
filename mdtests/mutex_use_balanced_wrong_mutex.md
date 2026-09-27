# Use authority for one mutex does not authorize another

```c filename=mutex_use_balanced_wrong_mutex.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; pthread_mutex_t other; };
void helper(struct holder *holder) {
    pthread_mutex_lock(&holder->other);
    pthread_mutex_unlock(&holder->other);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_use_balanced_wrong_mutex.c";

void helper(struct holder *holder) {
    owns mutex_use(&holder->mu);
} by {
    execute();
    simp();
}
```

```expect
fail: Requires owns mutex_use(&holder->other)
```
