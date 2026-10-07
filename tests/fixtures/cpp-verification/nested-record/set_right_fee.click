verifying "nested_record.cpp";

void FeeEnvelope_SetRightFee(struct FeeEnvelope* self, int64 next) {
    owns self->state.right.fee;
    views self->state.left.fee;
    views self->state.right.size;
    views self->stamp;
    ensures self->state.right.fee == next;
    ensures self->state.left.fee == old(self->state.left.fee);
    ensures self->state.right.size == old(self->state.right.size);
    ensures self->stamp == old(self->stamp);
} by { execute(); simp(); }
