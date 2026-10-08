verifying "loops.rs";

fn count(n: i32) -> i32 {
    requires n >= 0;
    ensures result == n;
} by {
    execute_until(assignment(i, 0)); step();
    have i == 0 by { simp(); }
    execute_until(loop(0));
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
    }
    execute(); simp();
}

fn accumulate(n: i32, value: i32) -> i32 {
    requires n >= 0;
    requires value == 1;
    ensures result == n;
} by {
    execute_until(assignment(i, 0)); step();
    have i == 0 by { simp(); }
    execute_until(loop(0));
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        invariant sum == i;
    }
    execute(); simp();
}

fn walk(bytes: &[u8]) -> usize {
    requires bytes_len <= 2147483647u64;
    views bytes[0..(int32)bytes_len];
    ensures result == bytes_len;
} by {
    execute_until(assignment(i, 0)); step();
    have i == 0 by { simp(); }
    execute_until(loop(0));
    loop {
        decreases bytes_len - i;
        invariant i <= bytes_len;
    }
    execute(); simp();
}
