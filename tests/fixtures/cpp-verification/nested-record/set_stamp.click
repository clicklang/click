verifying "nested_record.cpp";

void FeeEnvelope_SetStamp(struct FeeEnvelope* this, int next) {
    owns this->stamp;
    views this->state.left.fee;
    views this->state.left.size;
    views this->state.right.fee;
    views this->state.right.size;
    views this->state.generation;
    ensures this->stamp == next;
    ensures this->state.left.fee == old(this->state.left.fee);
    ensures this->state.left.size == old(this->state.left.size);
    ensures this->state.right.fee == old(this->state.right.fee);
    ensures this->state.right.size == old(this->state.right.size);
    ensures this->state.generation == old(this->state.generation);
} by { execute(); simp(); }
