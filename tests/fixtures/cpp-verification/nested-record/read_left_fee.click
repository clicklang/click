verifying "nested_record.cpp";

int64 FeeEnvelope::ReadLeftFee() const {
    views this->state.left.fee;
    ensures result == this->state.left.fee;
} by { execute(); simp(); }
