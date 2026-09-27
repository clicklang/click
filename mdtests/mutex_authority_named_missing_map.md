# A named guard binder must appear in the call map

```c filename=mutex_authority_named_missing_map.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; pthread_mutex_t other; };
void keep(struct holder *holder) {}
void caller(struct holder *holder) { keep(holder); }
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_authority_named_missing_map.c";

void keep(struct holder *holder) {
    owns g: mutex_guard(&holder->mu);
} by {
    execute();
    simp();
}

void caller(struct holder *holder) {
    owns g: mutex_guard(&holder->mu);
} by {
    step(keep(holder), {});
    execute();
    simp();
}
```

```expect
fail: call map omits `keep` binder `g`
```
