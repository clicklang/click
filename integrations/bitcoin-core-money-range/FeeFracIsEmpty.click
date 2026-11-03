verifying "bitcoin-src/src/util/feefrac.h";

bool FeeFrac::IsEmpty() const {
    views this->fee;
    views this->size;
    ensures this->fee == old(this->fee);
    ensures this->size == old(this->size);
    ensures result == (if old(this->size) == 0 { true } else { false });
    ensures result == true implies this->size == 0;
    ensures result == false implies this->size != 0;
} by {
    if this->size == 0 {
        step_until(function.exit);
        solve();
    } else {
        step_until(function.exit);
        solve();
    }
}
