# Nested helpers preserve two direct acquisition inputs

Each direct clause denotes its own acquisition. Calling another helper retains
both inputs without exposing acquisition numbers in the contract.

```c filename=guard_inputs.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void inner(struct holder *left, struct holder *right) {}
void outer(struct holder *left, struct holder *right) {
    inner(left, right);
    inner(right, left);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "guard_inputs.c";

void inner(struct holder *left, struct holder *right) {
    owns mutex_guard(&left->mu);
    owns mutex_guard(&right->mu);
} by { execute(); simp(); }

void outer(struct holder *left, struct holder *right) {
    owns mutex_guard(&left->mu);
    owns mutex_guard(&right->mu);
} by {
    step(inner(left, right), {});
    step(inner(right, left), {});
    step();
    simp();
}
```

```expect
pass
```
