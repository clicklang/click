# A mutex still initialized when a break leaves its scope names the loop

`holder` is declared in the loop body and its mutex is still initialized when
`break` leaves that scope. The refusal names the loop whose body ended.

```c filename=mutex_live_at_break.c
#include <pthread.h>
struct holder { int prefix; pthread_mutex_t mu; };
int run(void) {
    while (1) {
        struct holder holder;
        pthread_mutex_init(&holder.mu, 0);
        break;
    }
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";

verifying "mutex_live_at_break.c";
int32 run() { ensures result == 0; } by { execute(); simp(); }
```

```expect
fail: C statement at mutex_live_at_break.c:4:5: `while (1) {
```
