# Missing use authority names the required resource

```c filename=mutex_use_missing.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void helper(struct holder *holder) {}
void caller(struct holder *holder) { helper(holder); }
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "mutex_use_missing.c";
void helper(struct holder *holder) {
    owns mutex_use(&holder->mu);
}
void caller(struct holder *holder) {
    ensures 1 == 1;
} by { step(helper, {}); }
```

```expect
fail: Requires owns mutex_use(&holder->mu)
```
