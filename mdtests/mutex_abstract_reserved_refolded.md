# Abstract mutex inputs retain their storage reservation

This helper is verified independently, without a concrete initialization ledger.
The C store is fixed; its contract must establish separation from the mutex.

```c filename=mutex_abstract_reserved_refolded.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; int payload; };
void write_value(struct holder *holder, int *data) { *data = 7; }
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
resource lifetime(holder: struct holder*) {
    field tag: int32;
    owns mutex_live(&holder->mu);
}
verifying "mutex_abstract_reserved_refolded.c";
void write_value(struct holder *holder, int *data) {
    owns life: lifetime(holder);
    owns data[0..1];
} by { unfold(life); fold(life); execute(); simp(); }
```

```expect
fail: Requires separate(
```
