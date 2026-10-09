verifying "headers.rs";

fn final_header(bytes: &[u8]) -> usize {
    requires bytes.len() <= 2147483647u64;
    ensures result == bytes.len();
} by {
    execute_until(loop(0));
    loop {
        decreases bytes.len() - i;
        invariant i <= bytes.len();
    }
    execute(); simp();
}

fn negated(bytes: &[u8]) -> usize {
    requires bytes.len() <= 2147483647u64;
    ensures result == bytes.len();
} by {
    execute_until(loop(0));
    loop {
        decreases bytes.len() - i;
        invariant i <= bytes.len();
    }
    execute(); simp();
}
