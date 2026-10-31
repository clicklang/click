verifying "ranges.rs";

// A `for` over `start..end` holds the range in `iter_start` and `iter_end`:
// each iteration yields `iter_start` and advances it.

fn count_to(n: u32) -> u32 {
    ensures result == n;
} by {
    step_until(loop(0));
    loop {
        decreases iter_end - iter_start;
        invariant iter_end == n;
        invariant iter_start <= n;
        invariant total == iter_start;
    }
}

fn last_index(n: u32) -> u32 {
    ensures n == 0u32 implies result == 0u32;
    ensures n != 0u32 implies result == n - 1u32;
} by {
    step_until(loop(0));
    loop {
        decreases iter_end - iter_start;
        invariant iter_end == n;
        invariant iter_start <= n;
        invariant iter_start == 0u32 implies last == 0u32;
        invariant iter_start != 0u32 implies last == iter_start - 1u32;
    }
    have iter_start == n by solve();
}

fn span(a: i32, b: i32) -> i32 {
    requires 0i32 <= a and a <= b;
    ensures result == b - a;
} by {
    step_until(loop(0));
    loop {
        decreases iter_end - iter_start;
        invariant iter_end == b;
        invariant a <= iter_start and iter_start <= b;
        invariant count == iter_start - a;
    }
}

fn count_wide(n: u64) -> u64 {
    ensures result == n;
} by {
    step_until(loop(0));
    loop {
        decreases iter_end - iter_start;
        invariant iter_end == n;
        invariant iter_start <= n;
        invariant count == iter_start;
    }
}

fn count_signed_wide(n: i64) -> i64 {
    requires 0i64 <= n;
    ensures result == n;
} by {
    step_until(loop(0));
    loop {
        decreases iter_end - iter_start;
        invariant iter_end == n;
        invariant 0i64 <= iter_start and iter_start <= n;
        invariant count == iter_start;
    }
}

fn last_byte(bytes: &[u8]) -> u8 {
    views bytes[0..bytes.len()];
    ensures bytes.len() != 0u64 implies result == bytes[bytes.len() - 1u64];
} by {
    step_until(loop(0));
    loop {
        decreases iter_end - iter_start;
        views bytes[0..bytes.len()];
        invariant iter_end == bytes.len();
        invariant iter_start <= bytes.len();
        invariant iter_start != 0u64 implies last == bytes[iter_start - 1u64];
    }
    have iter_start == bytes.len() by solve();
}

// Nested loops' iterators share the source name `iter`, so each uses its
// compiler local's identity: `__rust_mir_7` outside, `__rust_mir_16` inside.
fn grid(n: u32, m: u32) -> u32 {
    requires n <= 1000u32 and m <= 1000u32;
    ensures result <= 1000u32 * n;
} by {
    step_until(loop(0));
    loop {
        decreases __rust_mir_7_end - __rust_mir_7_start;
        invariant __rust_mir_7_end == n;
        invariant __rust_mir_7_start <= n;
        invariant cells <= 1000u32 * __rust_mir_7_start;
        preserve by {
            step_until(loop(1));
            loop {
                decreases __rust_mir_16_end - __rust_mir_16_start;
                invariant __rust_mir_7_end == n;
                invariant __rust_mir_7_start <= n;
                invariant 1u32 <= __rust_mir_7_start;
                invariant __rust_mir_16_end == m;
                invariant __rust_mir_16_start <= m;
                invariant cells <= 1000u32 * (__rust_mir_7_start - 1u32) + __rust_mir_16_start;
            }
        }
    }
}
