verifying "nested_record.cpp";

int FeeEnvelope_ReadStamp(const struct FeeEnvelope* self) {
    views self->stamp;
    ensures result == self->stamp;
} by { execute(); simp(); }
