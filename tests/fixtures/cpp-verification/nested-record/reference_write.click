verifying "nested_record.cpp";

void SetFeeRef(struct FeeState& state, int64 next) {
    owns state.fee;
    ensures state.fee == next;
} by { execute(); simp(); }

void FeeEnvelope_SetLeftByReference(struct FeeEnvelope* self, int64 next) {
    owns self->state.left.fee;
    views self->state.right.fee;
    ensures self->state.left.fee == next;
    ensures self->state.right.fee == old(self->state.right.fee);
} by { execute(); simp(); }
