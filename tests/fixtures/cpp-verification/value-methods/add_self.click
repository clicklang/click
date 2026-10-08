verifying "value_methods.cpp";

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

int32 double_size(struct FeeFrac& value, int32& untouched) {
    owns untouched;
    ensures untouched == old(untouched);
    owns value.fee;
    owns value.size;
    requires -4611686018427387904 <= value.fee;
    requires value.fee <= 4611686018427387903;
    requires -1073741824 <= value.size;
    requires value.size <= 1073741823;
    ensures value.fee == old(value.fee) + old(value.fee);
    ensures value.size == old(value.size) + old(value.size);
    ensures result == value.size;
} by {
    execute();
    simp();
}
