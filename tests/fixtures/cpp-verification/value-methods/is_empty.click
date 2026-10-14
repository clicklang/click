verifying "value_methods.cpp";

bool FeeFrac::IsEmpty() const {
    owns this->fee;
    owns this->size;
    ensures this->fee == old(this->fee);
    ensures this->size == old(this->size);
    ensures result == (if old(this->size) == 0 { 1 } else { 0 });
} by {
    if this->size == 0 {
        execute();
        simp();
    } else {
        execute();
        simp();
    }
}
