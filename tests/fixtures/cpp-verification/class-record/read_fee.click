verifying "class_record.cpp";

int64 FeeRateState_ReadFee(const struct FeeRateState* this) {
    views this->fee;
    views this->size;
    ensures this->fee == old(this->fee);
    ensures this->size == old(this->size);
    ensures result == old(this->fee);
} by { execute(); simp(); }
