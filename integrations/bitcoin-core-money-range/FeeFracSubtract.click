verifying "bitcoin-src/src/util/feefrac.h";

void FeeFrac::operator-=(const FeeFrac& other) {
    owns this->fee;
    owns this->size;
    owns other.fee;
    owns other.size;
    requires -4611686018427387904 <= this->fee;
    requires this->fee <= 4611686018427387903;
    requires -4611686018427387904 <= other.fee;
    requires other.fee <= 4611686018427387903;
    requires -1073741824 <= this->size;
    requires this->size <= 1073741823;
    requires -1073741824 <= other.size;
    requires other.size <= 1073741823;
    ensures this->fee == old(this->fee) - old(other.fee);
    ensures this->size == old(this->size) - old(other.size);
    ensures other.fee == old(other.fee);
    ensures other.size == old(other.size);
} by {
    have separate(memory(this->fee), memory(other.size)) by close();
    step();
    have separate(region(0).footprint, at(region(0).entry, memory(other.size))) by {
        normalize() using { at(region(0).entry, separate(memory(this->fee), memory(other.size))); };
    }
    have at(region(0).exit, other.size) == at(region(0).entry, other.size) by close();
    have to_integer(this->size) - to_integer(other.size) <= 2147483647 by close() using {
        this->size <= 1073741823; -1073741824 <= other.size;
    };
    have to_integer(this->size) - to_integer(other.size) >= -2147483648 by close() using {
        -1073741824 <= this->size; other.size <= 1073741823;
    };
    step_until(function.exit);
    close();
}
