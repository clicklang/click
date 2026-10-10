verifying "split.rs";

fn left_length(bytes: &[u8], mid: usize) -> usize {
    requires mid <= bytes.len();
    ensures result == mid;
} by { execute(); simp(); }

fn right_length(bytes: &[u8], mid: usize) -> usize {
    requires mid <= bytes.len();
    ensures result == bytes.len() - mid;
} by { execute(); simp(); }

fn left_first(bytes: &[u8], mid: usize) -> u8 {
    requires mid <= bytes.len();
    requires 0u64 < mid;
    views bytes[0..bytes.len()];
    ensures result == bytes[0];
} by { execute(); simp(); }

fn right_first(bytes: &[u8], mid: usize) -> u8 {
    requires mid < bytes.len();
    views bytes[0..bytes.len()];
    ensures result == bytes[mid];
} by { execute(); simp(); }
