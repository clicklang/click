verifying "nested_record.cpp";

int64 ReadFeeRef(const struct FeeState& state) {
    views state.fee;
    ensures result == state.fee;
} by { execute(); simp(); }

int64 FeeEnvelope_ReadRightByReference(const struct FeeEnvelope* self) {
    views self->state.right.fee;
    ensures result == self->state.right.fee;
} by { execute(); simp(); }
