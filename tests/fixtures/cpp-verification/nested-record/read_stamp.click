verifying "nested_record.cpp";

int FeeEnvelope::ReadStamp() const {
    views this->stamp;
    ensures result == this->stamp;
} by { execute(); simp(); }
