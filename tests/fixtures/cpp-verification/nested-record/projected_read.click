verifying "nested_record.cpp";

int64 FeeState::ReadFee() const {
    views this->fee;
    ensures result == this->fee;
} by { execute(); solve(); }

int64 FeeEnvelope::ReadLeftByMethod() const {
    views this->state.left.fee;
    ensures result == this->state.left.fee;
} by { execute(); solve(); }
