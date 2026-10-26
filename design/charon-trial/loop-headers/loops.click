verifying "loops.rs";

fn count(n: i32) -> i32 {
    requires n >= 0;
    ensures result == n;
} by {
    step_until(region(4));
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
    }
    step_until(function.exit); solve();
}

fn accumulate(n: i32, value: i32) -> i32 {
    requires n >= 0;
    requires value == 1;
    ensures result == n;
} by {
    step_until(region(7));
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        invariant sum == i;
    }
    step_until(function.exit); solve();
}

fn walk(bytes: &[u8]) -> usize {
    requires bytes.len() <= 2147483647u64;
    views bytes[0..(bytes.len() as int32)];
    ensures result == bytes.len();
} by {
    step_until(region(4));
    loop {
        decreases bytes.len() - i;
        invariant i <= bytes.len();
    }
    step_until(function.exit); solve();
}

import click::integer;
