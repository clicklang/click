verifying "nested_record.cpp";

int64 FeeState_ReadFee(const struct FeeState* self) {
    views self->fee;
    ensures result == self->fee;
} by { execute(); simp(); }

int64 FeeEnvelope_ReadLeftByMethod(const struct FeeEnvelope* self) {
    views self->state.left.fee;
    ensures result == self->state.left.fee;
} by { execute(); simp(); }
