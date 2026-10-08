verifying "nested_record.cpp";

int64 ReadRightFee(const struct PairState& pair) {
    views pair.right.fee;
    ensures result == pair.right.fee;
} by { execute(); simp(); }
