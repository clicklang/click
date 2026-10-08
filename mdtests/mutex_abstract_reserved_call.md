# An assumed call cannot move abstract mutex inputs

This helper is verified independently, without a concrete initialization ledger.
It calls `touch`, which has only an assumed contract over the mutex resources.
An assumed contract that consumed a guard could leave a deposited control in two
places, so the call is refused. A verified `touch` is checked instead, as in
`authority_mutex_verified_helper_requires_separation.md`, where the storage
reservation still requires separation from the mutex.

```c filename=mutex_abstract_reserved_call.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; int payload; };
void touch(struct holder *holder, int *data);
void write_value(struct holder *holder, int *data) { touch(holder, data); }
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
resource lifetime(holder: struct holder*) {
    field tag: int32;
    owns mutex_live(&holder->mu);
}
verifying "mutex_abstract_reserved_call.c";
extern void touch(struct holder *holder, int *data) {
    owns mutex_live(&holder->mu);
    owns data[0..1];
}
void write_value(struct holder *holder, int *data) {
    owns mutex_live(&holder->mu);
    owns data[0..1];
} by { execute(); simp(); }
```

```expect
fail: its assumed contract changes a population or mutex resource
```
