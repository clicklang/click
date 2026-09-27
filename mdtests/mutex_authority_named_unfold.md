# A named mutex guard has no resource body to unfold

```c filename=mutex_authority_named_unfold.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; pthread_mutex_t other; };
void keep(struct holder *holder) {}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_authority_named_unfold.c";

void keep(struct holder *holder) {
    owns g: mutex_guard(&holder->mu);
} by {
    unfold(g);
    execute();
    simp();
}
```

```expect
fail: `mutex_guard` has no resource body to unfold
```
