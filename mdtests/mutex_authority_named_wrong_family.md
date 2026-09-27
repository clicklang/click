# A lifetime instance cannot supply a guard binder

```c filename=mutex_authority_named_wrong_family.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; pthread_mutex_t other; };
void keep(struct holder *holder) {}
void caller(struct holder *holder) { keep(holder); }
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_authority_named_wrong_family.c";

void keep(struct holder *holder) {
    owns g: mutex_guard(&holder->mu);
} by {
    execute();
    simp();
}

void caller(struct holder *holder) {
    owns life: mutex_live(&holder->mu);
} by {
    step(keep(holder), { g: life });
    execute();
    simp();
}
```

```expect
fail: binder `g` expects resource `mutex_guard`, but `life` is `mutex_live`
```
