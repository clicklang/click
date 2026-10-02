# Mutex storage ownership through transitive address equality

Initialization checks the original owner through the shared graph index.
Alignment is stated independently on the operated address; equality alone
must not grant storage authority. The unchanged synthetic C initializes and
destroys through the last pointer in the equality chain.

```c filename=mutex_alias.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
int run(struct holder *first, struct holder *middle, struct holder *last) {
    pthread_mutex_init(&last->mu, 0);
    pthread_mutex_destroy(&last->mu);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_alias.c";
int32 run(struct holder *first, struct holder *middle, struct holder *last) {
    requires first == middle;
    requires middle == last;
    requires aligned(&last->mu, 8);
    owns &first->mu;
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
pass
```
