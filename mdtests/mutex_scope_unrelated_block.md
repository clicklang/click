# A standalone block preserves an unrelated mutex

The unchanged C example now parses its standalone compound statement and
verifies that constructing and destroying the inner mutex preserves the
outer mutex for its later destruction.
Kernel scope-exit tests independently cover lifetime rejection.

```c filename=mutex_scope_unrelated.c
#include <pthread.h>
struct holder { int prefix; pthread_mutex_t mu; };
int run(void) {
    struct holder holder;
    pthread_mutex_init(&holder.mu, 0);
    {
        struct holder unrelated;
        pthread_mutex_init(&unrelated.mu, 0);
        pthread_mutex_destroy(&unrelated.mu);
    }
    pthread_mutex_destroy(&holder.mu);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";

verifying "mutex_scope_unrelated.c";
int32 run() { ensures result == 0; } by { execute(); simp(); }
```

```expect
pass
```
