# An assumed mutable contract over an initialized mutex is refused

This synthetic external call tests the contract boundary without requiring a
particular implementation. Its declared mutable footprint includes the mutex,
and its contract has no verified body, so the call is refused before its
footprint is considered. A verified helper with the same footprint is refused
for the mutex storage reservation instead, as
`authority_mutex_verified_helper_reserved_storage_rejected.md` checks.

```c filename=mutex_reserved_mutable_contract.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void touch(struct holder *holder);
int run(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    touch(holder);
    pthread_mutex_destroy(&holder->mu);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_reserved_mutable_contract.c";
extern void touch(struct holder *holder) {
    owns mutex_live(&holder->mu);
    owns holder->mu;
}
int32 run(struct holder *holder) {
    owns holder->mu;
    requires aligned(&holder->mu, 8);
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
fail: its assumed contract changes a population or mutex resource
```
