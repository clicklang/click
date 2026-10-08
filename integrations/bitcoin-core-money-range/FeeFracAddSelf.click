verifying "bitcoin-src/src/util/feefrac.h";

void FeeFrac_operator_add_assign(struct FeeFrac* this, const struct FeeFrac& other) {
    requires this == &other;
    owns this->fee;
    owns this->size;
    requires -4611686018427387904 <= this->fee;
    requires this->fee <= 4611686018427387903;
    requires -1073741824 <= this->size;
    requires this->size <= 1073741823;
    ensures this->fee == old(this->fee) + old(this->fee);
    ensures this->size == old(this->size) + old(this->size);
} by {
    execute();
    simp();
}
