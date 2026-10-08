verifying "nested_record.cpp";

int FeeEnvelope_ReadStamp(const struct FeeEnvelope* this) {
    views this->stamp;
    ensures result == this->stamp;
} by { execute(); simp(); }
