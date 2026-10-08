verifying "nested_record.cpp";

int32 ReadSizeRef(const int32& value) {
    views value;
    ensures result == value;
} by { execute(); simp(); }

int32 FeeEnvelope_ReadRightSizeByReference(const struct FeeEnvelope* self) {
    views self->state.right.size;
    ensures result == self->state.right.size;
} by { execute(); simp(); }
