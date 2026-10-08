# Abstract mutex inputs retain their storage reservation

This helper is verified independently, without a concrete initialization ledger.
The C store is fixed; its contract must establish separation from the mutex.

```c filename=mutex_abstract_reserved_entry_pointer.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; int payload; };
void write_value(struct holder *holder, struct holder *other, int *data) {
    holder = other;
    *data = 7;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
resource lifetime(holder: struct holder*) {
    field tag: int32;
    owns mutex_live(&holder->mu);
}
verifying "mutex_abstract_reserved_entry_pointer.c";
void write_value(struct holder *holder, struct holder *other, int *data) {
    owns mutex_live(&holder->mu);
    owns data[0..1];
    requires separate(memory(data[0..1]), memory(other->mu));
} by { execute(); simp(); }
```

```expect
fail: Requires separate(
```
