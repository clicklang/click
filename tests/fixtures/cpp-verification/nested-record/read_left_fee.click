verifying "nested_record.cpp";

int64 FeeEnvelope_ReadLeftFee(const struct FeeEnvelope* this) {
    views this->state.left.fee;
    ensures result == this->state.left.fee;
} by { execute(); simp(); }
