# mutex live rejects named binder

```c filename=mutex_use_rejects_named_binder.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void keep(struct holder *holder) {}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_use_rejects_named_binder.c";
void keep(struct holder *holder) { owns life: mutex_use(&holder->mu); } by { execute(); simp(); }
```

```expect
fail: named mutex_use binders are not supported yet
```
