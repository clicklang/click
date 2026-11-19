import click::cpp::span_state::{span_state};

// The catalog currently selects these contracts for dynamic std::span<int>.
template<class T> extern std::span<T>::span(const std::span<T>& source) {
    owns input: span_state(&source as (uint8*));
    produces copy: span_state(this as (uint8*));
    ensures input.data == old(input.data);
    ensures input.count == old(input.count);
    ensures copy.data == input.data;
    ensures copy.count == input.count;
}

template<class T> extern bool std::span<T>::empty() const {
    owns state: span_state(this as (uint8*));
    ensures state.data == old(state.data);
    ensures state.count == old(state.count);
    ensures state.count == 0u64 implies result;
    ensures state.count != 0u64 implies not result;
}
