verifying "split.rs";

fn left_length(bytes: &[u8], mid: usize) -> usize {
    requires mid <= bytes_len;
    requires mid <= 2147483647u64;
    ensures result == mid;
} by { execute(); simp(); }

fn right_length(bytes: &[u8], mid: usize) -> usize {
    requires mid <= bytes_len;
    requires mid <= 2147483647u64;
    ensures result == bytes_len - mid;
} by { execute(); simp(); }

fn left_first(bytes: &[u8], mid: usize) -> u8 {
    requires bytes_len <= 2147483647u64;
    requires mid <= bytes_len;
    requires 0u64 < mid;
    views bytes[0..(int32)(uint32)bytes_len];
    ensures result == bytes[0];
} by {
    have mid <= 2147483647u64 by { normalize() using { mid <= bytes_len; bytes_len <= 2147483647u64; } }
    have 0 < (int32)(uint32)mid by { simp() using { 0u64 < mid; mid <= 2147483647u64; } }
    have ((int32)(uint32)mid) <= (int32)(uint32)bytes_len by { simp() using { mid <= bytes_len; bytes_len <= 2147483647u64; } }
    have 1 <= (int32)(uint32)bytes_len by { arithmetic() using { 0 < (int32)(uint32)mid; ((int32)(uint32)mid) <= (int32)(uint32)bytes_len; } }
    execute(); simp();
}

fn right_first(bytes: &[u8], mid: usize) -> u8 {
    requires bytes_len <= 2147483647u64;
    requires mid < bytes_len;
    views bytes[0..(int32)(uint32)bytes_len];
    ensures result == bytes[(int32)(uint32)mid];
} by {
    have 0u64 < bytes_len - mid by { normalize() using { mid < bytes_len; } }
    have ((int32)(uint32)mid) < (int32)(uint32)bytes_len by { simp() using { mid < bytes_len; bytes_len <= 2147483647u64; } }
    execute(); simp();
}
