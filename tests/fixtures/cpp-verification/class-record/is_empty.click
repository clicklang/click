verifying "class_record.cpp";

bool FeeRateState_IsEmpty(const struct FeeRateState* this) {
    views this->fee;
    views this->size;
    ensures this->fee == old(this->fee);
    ensures this->size == old(this->size);
    ensures result == (if old(this->size) == 0 { 1 } else { 0 });
} by { execute(); simp(); }
