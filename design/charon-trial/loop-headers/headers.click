verifying "headers.rs";

uint64 final_header(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len <= 2147483647u64;
    ensures result == bytes_len;
} by {
    execute_until(loop(0));
    loop {
        decreases bytes_len - i;
        invariant i <= bytes_len;
    }
    execute(); simp();
}

uint64 negated(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len <= 2147483647u64;
    ensures result == bytes_len;
} by {
    execute_until(loop(0));
    loop {
        decreases bytes_len - i;
        invariant i <= bytes_len;
    }
    execute(); simp();
}
