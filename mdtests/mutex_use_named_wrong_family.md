# A guard cannot supply a named use permission

```c filename=mutex_authority_named_wrong_mutex.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; pthread_mutex_t other; };
void keep_other(struct holder *holder) {}
void caller(struct holder *holder) { keep_other(holder); }
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_authority_named_wrong_mutex.c";

void keep_other(struct holder *holder) {
    owns g: mutex_use(&holder->mu);
} by {
    execute();
    simp();
}

void caller(struct holder *holder) {
    owns g: mutex_guard(&holder->mu);
} by {
    step(keep_other(holder), { g: g });
    execute();
    simp();
}
```

```expect
fail: binder `g` expects resource `mutex_use`, but `g` is `mutex_guard`
```
