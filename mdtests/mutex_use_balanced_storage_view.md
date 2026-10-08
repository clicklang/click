# A use permission cannot write a stable view of mutex storage

```c filename=mutex_use_balanced_storage_view.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void helper(struct holder *holder) {
    pthread_mutex_lock(&holder->mu);
    pthread_mutex_unlock(&holder->mu);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_use_balanced_storage_view.c";
void helper(struct holder *holder) {
    owns mutex_use(&holder->mu);
    views holder->mu;
} by { execute(); simp(); }
```

```expect
fail: stable-view memory access conflicts with an active loan
```
