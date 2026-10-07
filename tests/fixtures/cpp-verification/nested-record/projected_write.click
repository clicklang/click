verifying "nested_record.cpp";

void FeeState_SetFee(struct FeeState* self, int64 next) {
    owns self->fee;
    ensures self->fee == next;
} by { execute(); simp(); }

void FeeEnvelope_SetRightByMethod(struct FeeEnvelope* self, int64 next) {
    owns self->state.right.fee;
    views self->state.left.fee;
    views self->state.right.size;
    ensures self->state.right.fee == next;
    ensures self->state.left.fee == old(self->state.left.fee);
    ensures self->state.right.size == old(self->state.right.size);
} by { execute(); simp(); }
