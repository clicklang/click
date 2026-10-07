verifying "nested_record.cpp";

int64 FeeEnvelope_ReadLeftFee(const struct FeeEnvelope* self) {
    views self->state.left.fee;
    ensures result == self->state.left.fee;
} by { execute(); simp(); }
