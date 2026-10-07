verifying "nested_record.cpp";

void FeeEnvelope_AddLeftSize(struct FeeEnvelope* self, int delta) {
    owns self->state.left.size;
    views self->state.right.size;
    requires 0 <= self->state.left.size;
    requires self->state.left.size <= 10;
    requires 0 <= delta;
    requires delta <= 10;
    ensures self->state.left.size == old(self->state.left.size) + delta;
    ensures self->state.right.size == old(self->state.right.size);
} by { execute(); simp(); }
