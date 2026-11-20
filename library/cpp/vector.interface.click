import click::cpp::vector_state::{vector_state};

unsigned long std::vector<unsigned char>::size() const {
    owns state: vector_state(this);
    ensures state.length == old(state.length);
    ensures state.data == old(state.data);
    ensures result == state.length;
}

bool std::vector<unsigned char>::empty() const {
    owns state: vector_state(this);
    ensures state.length == old(state.length);
    ensures state.data == old(state.data);
    ensures state.length == 0u64 implies result;
    ensures state.length != 0u64 implies not result;
}

const unsigned char* std::vector<unsigned char>::data() const {
    owns state: vector_state(this);
    ensures state.length == old(state.length);
    ensures state.data == old(state.data);
    ensures result == state.data;
}
