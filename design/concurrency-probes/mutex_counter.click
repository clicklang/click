target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_counter.c";

resource counter_state(counter: struct mutex_counter*) {
    field value: uint32;
    guarded_by counter->mutex;
    owns counter->value;
    fact counter->value == value;
}

void* increment_counter(void* argument) {
    owns access: mutex_use(
        &((struct mutex_counter*)argument)->mutex,
        counter_state((struct mutex_counter*)argument)
    );
    ensures result == 0;
} by {
    step();
    step();
    let { guard: guard, state: state } = step(
        pthread_mutex_lock(&counter->mutex), { access: access }
    );
    unfold(state);
    step();
    let restored = fold(counter_state(counter), { value: counter->value });
    step(pthread_mutex_unlock(&counter->mutex), {
        access: access, guard: guard, state: restored
    });
    step();
    simp();
}
