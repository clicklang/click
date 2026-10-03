target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_counter.c";

resource counter_state(counter: struct mutex_counter*) {
    field value: uint32;
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

int32 increment_twice(struct mutex_counter* counter) {
    owns &counter->mutex;
    requires aligned(&counter->mutex, 8);
    owns counter->value;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    step();
    let state = fold(counter_state(counter), { value: counter->value });
    let { lifetime: lifetime } = step(pthread_mutex_init(&counter->mutex, 0), { state: state });
    branch then { unfold(state); step(); simp(); } else {}
    step();
    branch then {
        step(pthread_mutex_destroy(&counter->mutex), { lifetime: lifetime });
        unfold(state);
        step();
        simp();
    } else {}
    step();
    branch then {
        step();
        step(pthread_mutex_destroy(&counter->mutex), { lifetime: lifetime });
        unfold(state);
        step();
        simp();
    } else {}
    step();
    step();
    step(pthread_mutex_destroy(&counter->mutex), { lifetime: lifetime });
    unfold(state);
    step();
    simp();
}
