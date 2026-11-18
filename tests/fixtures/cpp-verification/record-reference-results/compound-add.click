verifying "compound.cpp";

Counter& State::active() {
    owns this->delta;
    owns this->counter.value;
    ensures &result == &this->counter;
    ensures this->delta == 10;
    ensures this->counter.value == 40;
} by {
    step();
}

void add(State& state) {
    owns state.delta;
    owns state.counter.value;
    requires state.delta == 2;
    ensures state.delta == 10;
    ensures state.counter.value == 42;
} by {
    step();
}
