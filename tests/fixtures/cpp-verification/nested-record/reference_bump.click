verifying "nested_record.cpp";

void BumpSizeRef(int32* value) {
    owns value[0..1];
    requires 0 <= value[0];
    requires value[0] <= 10;
    ensures value[0] == old(value[0]) + 1;
} by { execute(); simp(); }

void FeeEnvelope_BumpLeftByReference(struct FeeEnvelope* self) {
    owns self->state.left.size;
    views self->state.right.size;
    requires 0 <= self->state.left.size;
    requires self->state.left.size <= 10;
    ensures self->state.left.size == old(self->state.left.size) + 1;
    ensures self->state.right.size == old(self->state.right.size);
} by { execute(); simp(); }
