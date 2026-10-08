verifying "bitcoin-src/src/util/feefrac.h";

void FeeFrac_operator_subtract_assign(struct FeeFrac* this, const struct FeeFrac& other) {
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
    execute();
    simp();
}
