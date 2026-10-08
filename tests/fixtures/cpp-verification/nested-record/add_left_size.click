verifying "nested_record.cpp";

void FeeEnvelope_AddLeftSize(struct FeeEnvelope* this, int delta) {
    owns this->state.left.size;
    views this->state.right.size;
    requires 0 <= this->state.left.size;
    requires this->state.left.size <= 10;
    requires 0 <= delta;
    requires delta <= 10;
    ensures this->state.left.size == old(this->state.left.size) + delta;
    ensures this->state.right.size == old(this->state.right.size);
} by { execute(); simp(); }
