verifying "nested_record.cpp";

int64 FeeState_ReadFee(const struct FeeState* this) {
    views this->fee;
    ensures result == this->fee;
} by { execute(); simp(); }

int64 FeeEnvelope_ReadLeftByMethod(const struct FeeEnvelope* this) {
    views this->state.left.fee;
    ensures result == this->state.left.fee;
} by { execute(); simp(); }
