import click::cpp::vector_state::{vector_state};

unsigned long std::vector<unsigned char>::size() const {
    owns state: vector_state(this);
    ensures state.length == old(state.length);
    ensures result == state.length;
}
