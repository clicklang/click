# Named guard inputs use ordinary call maps

```c filename=named_guard.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; };
void inner(struct counter *counter) {}
void outer(struct counter *counter) { inner(counter); inner(counter); }
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "named_guard.c";
void inner(struct counter *counter) {
    owns guard: mutex_guard(&counter->mu);
} by { execute(); simp(); }
void outer(struct counter *counter) {
    owns g: mutex_guard(&counter->mu);
} by {
    step(inner(counter), { guard: g });
    step(inner(counter), { guard: g });
    step();
    simp();
}
```

```expect
pass
```
