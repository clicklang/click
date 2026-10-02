# A mutex still initialized at a return names the return statement

`holder` leaves scope at the `return` with its mutex still initialized. The
refusal is about the path's end, and names the `return` it ended at.

```c filename=mutex_live_at_return.c
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

verifying "mutex_live_at_return.c";
int32 run() { ensures result == 0; } by { execute(); simp(); }
```

```expect
fail: C statement at mutex_live_at_return.c:6:5: `return 0;`
```
