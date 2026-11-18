struct Counter { int value; };
struct State {
    int delta;
    Counter counter;

    Counter& active() noexcept {
        delta = 10;
        counter.value = 40;
        return counter;
    }

    Counter& current() noexcept { return counter; }
};

void add(State& state) noexcept {
    state.active().value += state.delta;
}

void subtract(State& state, int delta) noexcept {
    state.current().value -= delta;
}
