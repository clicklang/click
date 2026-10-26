verifying "loops.rs";

fn count(n: i32) -> i32 {
    requires n >= 0;
    ensures result == n;
} by {
    step_until(assignment(i, 0)); step();
    have i == 0;
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
    }
    execute(); solve();
}

fn accumulate(n: i32, value: i32) -> i32 {
    requires n >= 0;
    requires value == 1;
    ensures result == n;
} by {
    step_until(assignment(i, 0)); step();
    have i == 0;
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        invariant sum == i;
    }
    execute(); solve();
}

fn walk(bytes: &[u8]) -> usize {
    views bytes[0..bytes.len()];
    ensures result == bytes.len();
} by {
    step_until(assignment(i, 0)); step();
    have i == 0;
    step_until(loop(0));
    loop {
        decreases bytes.len() - i;
        invariant i <= bytes.len();
    }
    execute(); solve();
}
