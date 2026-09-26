# mutex scope return

This is a synthetic C fixture for automatic-storage lifetime checking.

```c filename=mutex_scope_return.c
#include <pthread.h>
struct holder { int prefix; pthread_mutex_t mu; };
int run(void) {
    struct holder holder;
    pthread_mutex_init(&holder.mu, 0);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";

verifying "mutex_scope_return.c";
int32 run() { ensures result == 0; } by { execute(); simp(); }
```

```expect
fail: Cannot end local storage `holder` while mutex_live(
```
