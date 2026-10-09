# A worker writes protected memory reached through a pointer

The protected control owns a pointer cell and, through a named child, the
memory it points to, in another object. Nothing proves that memory separate
from the mutex's storage by address, and nothing needs to: initialization
consumed ownership of the storage, so memory the worker owns cannot reach it.

```c filename=mutex_protected_pointer_write.c
#include <pthread.h>
struct box { pthread_mutex_t mu; int *slot; };
void set_one(struct box *b) {
    pthread_mutex_lock(&b->mu);
    *b->slot = 1;
    pthread_mutex_unlock(&b->mu);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_protected_pointer_write.c";
resource target(q: int32*) {
    field v: int32;
    owns *q;
    fact *q == v;
}
resource box_state(b: struct box*) {
    field v: int32;
    owns b->slot;
    owns held: target(b->slot);
    fact held.v == v;
}
void set_one(struct box *b) {
    owns access: mutex_use(&b->mu, box_state(b));
} by {
    let { guard: guard, state: state } = step(pthread_mutex_lock(&b->mu), { access: access });
    let { v: v, held: held } = unfold(state);
    unfold(held);
    step();
    let written = fold(target(b->slot), { v: *b->slot });
    let restored = fold(box_state(b), { v: *b->slot }, { held: written });
    step(pthread_mutex_unlock(&b->mu), { access: access, guard: guard, state: restored });
    step();
    simp();
}
```

```expect
pass
```
