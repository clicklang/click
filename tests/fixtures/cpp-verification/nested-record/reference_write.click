verifying "nested_record.cpp";

void SetFeeRef(struct FeeState& state, int64 next) {
    owns state.fee;
    ensures state.fee == next;
} by { execute(); simp(); }

void FeeEnvelope_SetLeftByReference(struct FeeEnvelope* this, int64 next) {
    owns this->state.left.fee;
    views this->state.right.fee;
    ensures this->state.left.fee == next;
    ensures this->state.right.fee == old(this->state.right.fee);
} by { execute(); simp(); }
