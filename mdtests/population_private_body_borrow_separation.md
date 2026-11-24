# A private body can open with separated stack and external borrows

```c filename=population_private_body_borrow_separation.c
#include <pthread.h>
#include <stddef.h>
void *reader(void *p) { (void)p; return NULL; }
int update(int *pool, int *p, int *q) {
    int task[1] = {1};
    pthread_t first;
    int status = pthread_create(&first, NULL, reader, task);
    if (status != 0) { return 0; }
    p[0] = 7;
    pthread_join(first, NULL);
    return 7;
}
```
```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
authorized resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
verifying "population_private_body_borrow_separation.c";
void *reader(void *p) { views (p as (int32 *))[0..1]; }
int32 update(int32 *pool, int32 *p, int32 *q) {
    owns slot(pool, p);
    views q[0..1];
    requires separate(memory(p[0..1]), memory(q[0..1]));
    ensures result == 0 or result == 7;
} by {
    step_until(statement(3).entry);
    branch { true => { step(); close(); } false => {} }
    have separate(memory(p[0..1]), memory(q[0..1]) * memory(task[0..1])) by { close(); }
    with(slot(pool, p)) { step(); }
}
```
```expect
pass
```
