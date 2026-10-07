verifying "class_record.cpp";

bool FeeRateState_IsEmpty(const struct FeeRateState* self) {
    views self->fee;
    views self->size;
    ensures self->fee == old(self->fee);
    ensures self->size == old(self->size);
    ensures result == (if old(self->size) == 0 { 1 } else { 0 });
} by { execute(); simp(); }
