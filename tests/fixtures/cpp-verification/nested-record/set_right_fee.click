verifying "nested_record.cpp";

void FeeEnvelope_SetRightFee(struct FeeEnvelope* this, int64 next) {
    owns this->state.right.fee;
    views this->state.left.fee;
    views this->state.right.size;
    views this->stamp;
    ensures this->state.right.fee == next;
    ensures this->state.left.fee == old(this->state.left.fee);
    ensures this->state.right.size == old(this->state.right.size);
    ensures this->stamp == old(this->stamp);
} by { execute(); simp(); }
