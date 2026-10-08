verifying "bitcoin-src/src/util/feefrac.h";

void FeeFrac_operator_subtract_assign(struct FeeFrac* this, const struct FeeFrac& other) {
    requires this == &other;
    owns this->fee;
    owns this->size;
    ensures this->fee == 0i64;
    ensures this->size == 0;
} by {
    execute();
    simp();
}
