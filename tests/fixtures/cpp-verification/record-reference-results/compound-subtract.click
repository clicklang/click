verifying "compound.cpp";

Counter& State::current() {
    views this->counter.value;
    ensures &result == &this->counter;
}

void subtract(State& state, int32 delta) {
    owns state.counter.value;
    requires state.counter.value == 40;
    requires delta == 2;
    ensures state.counter.value == 38;
} by {
    step();
}
