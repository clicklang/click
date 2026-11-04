verifying "ranges.rs";

// A `for` over `start..end` is read through the range's own fields,
// `iter.start` and `iter.end`: each iteration yields `iter.start` and
// advances it.

fn count_to(n: u32) -> u32 {
    ensures result == n;
} by {
    step_until(loop(0));
    loop {
        decreases iter.end - iter.start;
        invariant iter.end == n;
        invariant iter.start <= n;
        invariant total == iter.start;
    }
}

fn span(a: i32, b: i32) -> i32 {
    requires 0i32 <= a and a <= b;
    ensures result == b - a;
} by {
    step_until(loop(0));
    loop {
        decreases iter.end - iter.start;
        invariant iter.end == b;
        invariant a <= iter.start and iter.start <= b;
        invariant count == iter.start - a;
    }
}

fn count_signed_wide(n: i64) -> i64 {
    requires 0i64 <= n;
    ensures result == n;
} by {
    step_until(loop(0));
    loop {
        decreases iter.end - iter.start;
        invariant iter.end == n;
        invariant 0i64 <= iter.start and iter.start <= n;
        invariant count == iter.start;
    }
}

fn last_byte(bytes: &[u8]) -> u8 {
    views bytes[0..bytes.len()];
    ensures bytes.len() != 0u64 implies result == bytes[bytes.len() - 1u64];
} by {
    step_until(loop(0));
    loop {
        decreases iter.end - iter.start;
        views bytes[0..bytes.len()];
        invariant iter.end == bytes.len();
        invariant iter.start <= bytes.len();
        invariant iter.start != 0u64 implies last == bytes[iter.start - 1u64];
    }
    have loop(0).iter.start == bytes.len() by solve();
}

// In nested loops, `iter` is the inner loop's iterator inside it; the outer
// one is `loop(0).iter` there.
fn grid(n: u32, m: u32) -> u32 {
    requires n <= 1000u32 and m <= 1000u32;
    ensures result <= 1000u32 * n;
} by {
    step_until(loop(0));
    loop {
        decreases iter.end - iter.start;
        invariant iter.end == n;
        invariant iter.start <= n;
        invariant cells <= 1000u32 * iter.start;
        preserve by {
            step_until(loop(1));
            loop {
                decreases iter.end - iter.start;
                invariant loop(0).iter.end == n;
                invariant loop(0).iter.start <= n;
                invariant 1u32 <= loop(0).iter.start;
                invariant iter.end == m;
                invariant iter.start <= m;
                invariant cells <= 1000u32 * (loop(0).iter.start - 1u32) + iter.start;
            }
        }
    }
}
