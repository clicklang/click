# Owned memory is separate from an input mutex's storage

This helper is verified independently, without a concrete initialization ledger.
Initialization consumed ownership of the mutex's storage bytes, so no owned
memory reaches them, and the store into owned `data` needs no separation
premise. A reserved automatic mutex is protected where it is initialized: its
owner checks every footprint it transfers against it.

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
pass
```
