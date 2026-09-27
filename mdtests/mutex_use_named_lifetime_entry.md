# A named entry lifetime lends a use permission and remains owned

```c filename=mutex_use_named_lifetime_entry.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void helper(struct holder *holder) {
    pthread_mutex_lock(&holder->mu);
    pthread_mutex_unlock(&holder->mu);
}
void caller(struct holder *holder) { helper(holder); helper(holder); }
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_use_named_lifetime_entry.c";

void helper(struct holder *holder) {
    owns access: mutex_use(&holder->mu);
} by { execute(); simp(); }

void caller(struct holder *holder) {
    owns lifetime: mutex_live(&holder->mu);
} by {
    step(helper(holder), { access: lifetime });
    step(helper(holder), { access: lifetime });
    step();
    simp();
}
```

```expect
pass
```
