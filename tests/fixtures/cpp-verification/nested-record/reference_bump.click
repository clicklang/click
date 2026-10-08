verifying "nested_record.cpp";

void BumpSizeRef(int32& value) {
    owns value;
    requires 0 <= value;
    requires value <= 10;
    ensures value == old(value) + 1;
} by { execute(); simp(); }

void FeeEnvelope_BumpLeftByReference(struct FeeEnvelope* this) {
    owns this->state.left.size;
    views this->state.right.size;
    requires 0 <= this->state.left.size;
    requires this->state.left.size <= 10;
    ensures this->state.left.size == old(this->state.left.size) + 1;
    ensures this->state.right.size == old(this->state.right.size);
} by { execute(); simp(); }
