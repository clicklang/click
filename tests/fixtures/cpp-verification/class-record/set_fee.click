verifying "class_record.cpp";

void FeeRateState_SetFee(struct FeeRateState* this, int64 next) {
    owns this->fee;
    views this->size;
    ensures this->fee == next;
    ensures this->size == old(this->size);
} by { execute(); simp(); }
