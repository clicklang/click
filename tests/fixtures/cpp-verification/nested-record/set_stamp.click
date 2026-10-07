verifying "nested_record.cpp";

void FeeEnvelope_SetStamp(struct FeeEnvelope* self, int next) {
    owns self->stamp;
    views self->state.left.fee;
    views self->state.left.size;
    views self->state.right.fee;
    views self->state.right.size;
    views self->state.generation;
    ensures self->stamp == next;
    ensures self->state.left.fee == old(self->state.left.fee);
    ensures self->state.left.size == old(self->state.left.size);
    ensures self->state.right.fee == old(self->state.right.fee);
    ensures self->state.right.size == old(self->state.right.size);
    ensures self->state.generation == old(self->state.generation);
} by { execute(); simp(); }
