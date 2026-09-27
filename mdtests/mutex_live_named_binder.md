# Named lifecycle authority preserves its initialization

```c filename=mutex_live_rejects_named_binder.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void keep(struct holder *holder) {}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_live_rejects_named_binder.c";
void keep(struct holder *holder) { owns life: mutex_live(&holder->mu); } by { execute(); simp(); }
```

```expect
pass
```
