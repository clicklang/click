verifying "exits.rs";

// A `return` from a loop body runs to the function exit as a C `return`
// does; a labeled `break` or `continue` leaves each loop it crosses through
// an escape flag the enclosing loop checks. Nested loops' iterators share
// the source name `iter`, so `first_row` names each by its compiler local.

fn has_zero(xs: &[u8]) -> bool {
    views xs[0..xs.len()];
    ensures result implies xs.len() != 0u64;
} by {
    step_until(loop(0));
    loop {
        decreases xs.len() - i;
        views xs[0..xs.len()];
        invariant i <= xs.len();
    }
}

fn position(xs: &[u8], v: u8) -> usize {
    views xs[0..xs.len()];
    ensures result <= xs.len();
    ensures result < xs.len() implies xs[result] == v;
} by {
    step_until(loop(0));
    loop {
        decreases iter_end - iter_start;
        views xs[0..xs.len()];
        invariant iter_end == xs.len();
        invariant iter_start <= xs.len();
    }
}

fn find_pair(n: u32, m: u32) -> u32 {
    requires n <= 1000u32 and m <= 1000u32;
    ensures result <= n;
} by {
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant i <= n;
        preserve by {
            step_until(loop(1));
            loop {
                decreases m - j;
                invariant i < n;
                invariant j <= m;
            }
        }
    }
}

fn first_hit(n: u32, m: u32) -> u32 {
    ensures result <= n;
} by {
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant i <= n;
        invariant found <= n;
        preserve by {
            step_until(loop(1));
            loop {
                decreases m - j;
                invariant i < n;
                invariant found <= n;
                invariant j <= m;
            }
        }
    }
}

fn first_row(n: u32, m: u32) -> u32 {
    ensures result <= n;
} by {
    step_until(loop(0));
    loop {
        decreases __rust_mir_7_end - __rust_mir_7_start;
        invariant __rust_mir_7_end == n;
        invariant __rust_mir_7_start <= n;
        invariant row <= n;
        preserve by {
            step_until(loop(1));
            loop {
                decreases __rust_mir_16_end - __rust_mir_16_start;
                invariant __rust_mir_7_end == n;
                invariant __rust_mir_7_start <= n;
                invariant 1u32 <= __rust_mir_7_start;
                invariant row <= n;
            }
        }
    }
}

fn skip_rows(n: u32, m: u32) -> u32 {
    ensures result <= m;
} by {
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant i <= n;
        invariant count <= m;
        preserve by {
            step_until(loop(1));
            loop {
                decreases m - j;
                invariant 1u32 <= i and i <= n;
                invariant count <= m;
                invariant j <= m;
            }
        }
    }
}
