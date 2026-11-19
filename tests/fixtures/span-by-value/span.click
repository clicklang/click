verifying "span-probe.cpp";

import click::cpp::span_state::{span_state};

bool is_empty(std::span<int> span) {
    consumes state: span_state(&span as (uint8*));
    ensures old(state.count) == 0u64 implies result;
    ensures old(state.count) != 0u64 implies not result;
} by {
    step(std::span<int>::empty, { state: state });
}

bool probe(const std::span<int>& source) {
    owns input: span_state(&source as (uint8*));
    ensures input.data == old(input.data);
    ensures input.count == old(input.count);
    ensures input.count == 0u64 implies result;
    ensures input.count != 0u64 implies not result;
} by {
    step();
    let { copy: copied } = step(std::span<int>::span, { input: input });
    step();
    step(is_empty, { state: copied });
}
