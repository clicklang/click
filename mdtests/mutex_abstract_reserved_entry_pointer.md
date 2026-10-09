# Owned memory is separate from an input mutex's storage

This helper is verified independently, without a concrete initialization ledger.
Initialization consumed ownership of the mutex's storage bytes, so no owned
memory reaches them, and the store into owned `data` needs no separation
premise. A reserved automatic mutex is protected where it is initialized: its
owner checks every footprint it transfers against it.

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
pass
```
