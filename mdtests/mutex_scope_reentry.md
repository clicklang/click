# mutex scope reentry

This is a synthetic C fixture for automatic-storage lifetime checking.

```c filename=mutex_scope_reentry.c
#include <pthread.h>
struct holder { int prefix; pthread_mutex_t mu; };
int run(void) {
    int i = 0;
    while (i < 2) {
        struct holder holder;
        pthread_mutex_init(&holder.mu, 0);
        pthread_mutex_destroy(&holder.mu);
        i++;
        continue;
    }
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";

verifying "mutex_scope_reentry.c";
int32 run() { ensures result == 0; } by { execute(); simp(); }
```

```expect
pass
```
