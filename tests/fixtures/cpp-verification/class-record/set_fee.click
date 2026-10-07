verifying "class_record.cpp";

void FeeRateState_SetFee(struct FeeRateState* self, int64 next) {
    owns self->fee;
    views self->size;
    ensures self->fee == next;
    ensures self->size == old(self->size);
} by { execute(); simp(); }
