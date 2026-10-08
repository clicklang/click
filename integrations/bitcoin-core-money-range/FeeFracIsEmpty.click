verifying "bitcoin-src/src/util/feefrac.h";

bool FeeFrac_IsEmpty(const struct FeeFrac* this) {
    views this->fee;
    views this->size;
    ensures this->fee == old(this->fee);
    ensures this->size == old(this->size);
    ensures result == (if old(this->size) == 0 { 1 } else { 0 });
    ensures result != 0 implies this->size == 0;
    ensures result == 0 implies this->size != 0;
} by {
    if this->size == 0 {
        execute();
        simp();
    } else {
        execute();
        simp();
    }
}
