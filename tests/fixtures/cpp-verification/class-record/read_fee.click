verifying "class_record.cpp";

int64 FeeRateState_ReadFee(const struct FeeRateState* self) {
    views self->fee;
    views self->size;
    ensures self->fee == old(self->fee);
    ensures self->size == old(self->size);
    ensures result == old(self->fee);
} by { execute(); simp(); }
