verifying "class_record.cpp";

int64 FeeRateState::ReadFee() const {
    views this->fee;
    views this->size;
    ensures this->fee == old(this->fee);
    ensures this->size == old(this->size);
    ensures result == old(this->fee);
} by { execute(); simp(); }
