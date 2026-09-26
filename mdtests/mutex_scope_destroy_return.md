# Destroying a stack mutex permits function return

This synthetic example exercises function-frame retirement. It does not cover
the unsupported standalone nested blocks recorded in the adjacent fixtures.

```c filename=mutex_scope_destroy_return.c
#include <pthread.h>
struct holder { int prefix; pthread_mutex_t mu; };
int run(void) {
    struct holder holder;
    pthread_mutex_init(&holder.mu, 0);
    pthread_mutex_lock(&holder.mu);
    pthread_mutex_unlock(&holder.mu);
    pthread_mutex_destroy(&holder.mu);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_scope_destroy_return.c";
int32 run() { ensures result == 0; } by { execute(); simp(); }
```

```expect
pass
```
