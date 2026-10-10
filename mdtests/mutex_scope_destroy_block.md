# Destroy a mutex inside a standalone block

The unchanged C example now parses its standalone compound statement and
verifies the init, lock, unlock, and destroy sequence before returning.
Kernel scope-exit tests independently cover lifetime rejection.

```c filename=mutex_scope_destroy.c
#include <pthread.h>
struct holder { int prefix; pthread_mutex_t mu; };
int run(void) {
    {
        struct holder holder;
        pthread_mutex_init(&holder.mu, 0);
        pthread_mutex_lock(&holder.mu);
        pthread_mutex_unlock(&holder.mu);
        pthread_mutex_destroy(&holder.mu);
    }
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";

verifying "mutex_scope_destroy.c";
int32 run() { ensures result == 0; } by { execute(); simp(); }
```

```expect
pass
```
