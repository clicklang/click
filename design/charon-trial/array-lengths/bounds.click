verifying "bounds.rs";

uint64 signed_len(const int32* values) {
    ensures result == 1024u64;
} by { execute(); simp(); }

uint64 million_len(const uint32* values) {
    ensures result == 1000000u64;
} by { execute(); simp(); }

uint64 empty_len(const uint32* values) {
    ensures result == 0u64;
} by { execute(); simp(); }
