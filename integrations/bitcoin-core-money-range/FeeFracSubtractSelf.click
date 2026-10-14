verifying "bitcoin-src/src/util/feefrac.h";

void FeeFrac::operator-=(const FeeFrac& other) {
    requires this == &other;
    owns this->fee;
    owns this->size;
    ensures this->fee == 0i64;
    ensures this->size == 0;
} by {
    execute();
    simp();
}
