verifying "bitcoin-src/src/util/feefrac.h";

void FeeFrac::operator-=(const FeeFrac& other) {
    requires this == &other;
    owns this->fee;
    owns this->size;
    ensures this->fee == 0i64;
    ensures this->size == 0;
} by {
    step();
    have other.size == this->size by { rewrite(&other, this); close(); }
    step_until(function.exit);
    close();
}
