# A verified helper cannot own a live mutex's storage beside its lifetime

The authority-mode form of `mutex_reserved_mutable_contract.md`. There
`touch` is an assumed contract, which authority semantics refuse when it
moves mutex resources. Here `touch` is a verified helper whose contract owns
both the mutex lifetime and the mutex's raw storage; the lifetime reserves
that storage, so the two cannot be held together and the call is refused.

```c filename=authority_mutex_verified_helper_reserved_storage_rejected.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void touch(struct holder *holder) { }
int run(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    touch(holder);
    pthread_mutex_destroy(&holder->mu);
    return 0;
}
```

```click resource_semantics=authority
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "authority_mutex_verified_helper_reserved_storage_rejected.c";
void touch(struct holder *holder) {
    owns mutex_live(&holder->mu);
    owns holder->mu;
} by { execute(); simp(); }
int32 run(struct holder *holder) {
    owns holder->mu;
    requires aligned(&holder->mu, 8);
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
fail: Requires separate(memory(holder[0..40]), memory(holder[0..40])); initialized mutex storage is reserved
```
