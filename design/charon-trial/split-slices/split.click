verifying "split.rs";

fn left_length(bytes: &[u8], mid: usize) -> usize {
    requires mid <= bytes.len();
    requires mid <= 2147483647u64;
    ensures result == mid;
} by { execute(); simp(); }

fn right_length(bytes: &[u8], mid: usize) -> usize {
    requires mid <= bytes.len();
    requires mid <= 2147483647u64;
    ensures result == bytes.len() - mid;
} by { execute(); simp(); }

fn left_first(bytes: &[u8], mid: usize) -> u8 {
    requires bytes.len() <= 2147483647u64;
    requires mid <= bytes.len();
    requires 0u64 < mid;
    views bytes[0..bytes.len()];
    ensures result == bytes[0];
} by {
    have mid <= 2147483647u64 by { normalize() using { mid <= bytes.len(); bytes.len() <= 2147483647u64; } }
    have 0 < (int32)(uint32)mid by { simp() using { 0u64 < mid; mid <= 2147483647u64; } }
    have ((int32)(uint32)mid) <= (int32)(uint32)bytes.len() by { simp() using { mid <= bytes.len(); bytes.len() <= 2147483647u64; } }
    have 1 <= (int32)(uint32)bytes.len() by { arithmetic() using { 0 < (int32)(uint32)mid; ((int32)(uint32)mid) <= (int32)(uint32)bytes.len(); } }
    execute(); simp();
}

fn right_first(bytes: &[u8], mid: usize) -> u8 {
    requires bytes.len() <= 2147483647u64;
    requires mid < bytes.len();
    views bytes[0..bytes.len()];
    ensures result == bytes[mid];
} by {
    have 0u64 < bytes.len() - mid by { normalize() using { mid < bytes.len(); } }
    have ((int32)(uint32)mid) < (int32)(uint32)bytes.len() by { simp() using { mid < bytes.len(); bytes.len() <= 2147483647u64; } }
    execute(); simp();
}
