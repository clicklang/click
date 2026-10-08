verifying "nested_record.cpp";

void FeeState_SetFee(struct FeeState* this, int64 next) {
    owns this->fee;
    ensures this->fee == next;
} by { execute(); simp(); }

void FeeEnvelope_SetRightByMethod(struct FeeEnvelope* this, int64 next) {
    owns this->state.right.fee;
    views this->state.left.fee;
    views this->state.right.size;
    ensures this->state.right.fee == next;
    ensures this->state.left.fee == old(this->state.left.fee);
    ensures this->state.right.size == old(this->state.right.size);
} by { execute(); simp(); }
