# A parent cannot lock its own mutex after joining a typed `mutex_use` worker

## Violated invariant

After `pthread_join` returns, the worker's use of the mutex is over and the
parent holds the lifecycle authority `mutex_live` again, so a plain
`pthread_mutex_lock` by the parent must be accepted exactly as it is before
the worker is created (`docs/internals/mutex-resource-contracts.md`;
`mdtests/modeled_pthread_mutex_parent_interference.md` shows the parent
locking while the worker is pending).

Under `runtime "modeled-pthread"` with a typed worker contract
`owns access: mutex_use(&c->mu, counter_state(c))`, the join leaves a phantom
in the parent's resource context. `--trace-proof run` shows the join step
doing

```text
resource gained: owns mutex_live(&counter->mu)
resource lost:   owns mutex_use(&counter->mu)
resource gained: owns mutex_use(&counter->mu)
```

so the parent holds both `mutex_live` and an `owns mutex_use(&counter->mu)`
with no loan binding. The phantom comes from `ThreadContext::join`
(`src/kernel/threads.rs`, near line 1010) composing `completion.outputs`,
which carries the worker's preserved `access` use, into the parent frame,
while `recover_suspended_views` separately restores the lifecycle authority.
`MutexContext::acquire_current` (`src/kernel/mutexes.rs:1615`) then selects
the phantom through `mutex_use_candidate_at`, fails on its missing binding,
and never falls through to the lifecycle `acquire`. The phantom also survives
`pthread_mutex_destroy`, which reports only `mutex_live` lost. Every attempt
to use the phantom (a second worker, a helper, a wrapper resource) was
refused for lack of loan backing, so this is a wrong refusal and a
resource-context hygiene defect rather than a reproduced soundness hole.

## Reproduction

```c filename=e111b.c
#include <pthread.h>
#include <stddef.h>
struct counter { pthread_mutex_t mu; unsigned int value; };
void *worker(void *argument) {
    struct counter *counter = argument;
    pthread_mutex_lock(&counter->mu);
    counter->value = counter->value + 1u;
    pthread_mutex_unlock(&counter->mu);
    return NULL;
}
unsigned int run(struct counter *counter) {
    pthread_t thread;
    pthread_mutex_init(&counter->mu, NULL);
    if (pthread_create(&thread, NULL, worker, counter) != 0) {
        pthread_mutex_destroy(&counter->mu);
        return 0u;
    }
    pthread_join(thread, NULL);
    pthread_mutex_lock(&counter->mu);
    pthread_mutex_unlock(&counter->mu);
    pthread_mutex_destroy(&counter->mu);
    return 1u;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "e111b.c";
resource counter_state(counter: struct counter*) {
    field value: uint32;
    owns counter->value;
    fact counter->value == value;
}
void* worker(void* argument) {
    owns access: mutex_use(&((struct counter*)argument)->mu, counter_state((struct counter*)argument));
    ensures result == 0;
} by {
    step();
    step();
    let { guard: guard, state: state } = step(pthread_mutex_lock(&counter->mu), { access: access });
    unfold(state);
    step();
    let restored = fold(counter_state(counter), { value: counter->value });
    step(pthread_mutex_unlock(&counter->mu), { access: access, guard: guard, state: restored });
    step();
    simp();
}
uint32 run(struct counter* counter) {
    owns &counter->mu;
    requires aligned(&counter->mu, 8);
    owns initial: counter_state(counter);
    ensures result == 0 or result == 1;
} by {
    step();
    let { lifetime: lifetime } = step(pthread_mutex_init(&counter->mu, 0), { state: initial });
    step();
    branch then {
        step(pthread_mutex_destroy(&counter->mu), { lifetime: lifetime });
        step();
        simp();
    } else {}
    step();
    step();
    step();
    step(pthread_mutex_destroy(&counter->mu), { lifetime: lifetime });
    step();
    simp();
}
```

Observed on 2026-10-07:

```text
proof error:
  `run.contract` tactic 3
  `step()` could not verify C operation
  Requires owns mutex_use(&counter->mu)
  `pthread_mutex_lock(&counter->mu);`
```

## Intended regression

The program above as a positive mdtest (`modeled_pthread_lock_after_join`),
plus a kernel test asserting that after a join the parent frame holds no
`mutex_use` fact for a mutex it holds `mutex_live` for, and that
`pthread_mutex_destroy` leaves no mutex fact behind.

## Acceptance criteria

- Joining a typed `mutex_use` worker restores the parent's `mutex_live`
  without leaving the worker's use fact in the parent's frame.
- `acquire_current` falls through to the lifecycle authority when the only
  use candidate has no binding, or no such candidate exists any more.
- `scripts/check.sh` passes.
