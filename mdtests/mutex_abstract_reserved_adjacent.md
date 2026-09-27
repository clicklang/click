# Folded input reservations permit adjacent payload writes

```c filename=mutex_abstract_reserved_adjacent.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; int payload; };
void write_value(struct holder *holder) { holder->payload = 7; }
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
resource lifetime(holder: struct holder*) {
    field tag: int32;
    owns mutex_live(&holder->mu);
}
verifying "mutex_abstract_reserved_adjacent.c";
void write_value(struct holder *holder) {
    owns life: lifetime(holder);
    owns holder->payload;
    ensures holder->payload == 7;
} by { execute(); simp(); }
```

```expect
pass
```
