# A live mutex's storage cannot be written

Initialization consumed ownership of the mutex's storage bytes, so a store into
them is refused until `pthread_mutex_destroy` returns that ownership.

```c filename=mutex_storage_store_while_live_rejected.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; int value; };
int run(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    unsigned char *bytes = (unsigned char *)&holder->mu;
    bytes[0] = 1;
    pthread_mutex_destroy(&holder->mu);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_storage_store_while_live_rejected.c";
int32 run(struct holder *holder) {
    owns holder->mu;
    requires aligned(&holder->mu, 8);
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
fail: initialized mutex storage is reserved until pthread_mutex_destroy
```
