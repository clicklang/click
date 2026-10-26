verifying "nested_record.cpp";

int64 ReadFeeRef(const struct FeeState& state) {
    views state.fee;
    ensures result == state.fee;
}

int64 FeeEnvelope::ReadRightByReference() const {
    views this->state.right.fee;
    ensures result == this->state.right.fee;
}
