verifying "inclusive.rs";

// A `for` over `start..=end` holds the range in `iter_start` and `iter_end`
// and whether it has yielded `end` in `iter_done`: each iteration yields
// `iter_start` and advances it while it is below `end`, and at `end` sets
// `iter_done` instead, so `start` never passes `end`.

fn count_through(n: u32) -> u32 {
    requires n < 4294967295u32;
    ensures result == n + 1;
} by {
    step_until(loop(0));
    loop {
        decreases iter_end - iter_start + 1 - iter_done;
        invariant iter_end == n;
        invariant iter_start <= n;
        invariant 0 <= iter_done and iter_done <= 1;
        invariant iter_done != 0 implies iter_start == n and total == n + 1;
        invariant total == iter_start + iter_done;
    }
}

// A range through the type's maximum yields it once and stops: `iter_start`
// stays at 255 rather than wrapping.
fn every_byte() -> u32 {
    ensures result == 256u32;
} by {
    step_until(loop(0));
    loop {
        decreases iter_end - iter_start + 1 - iter_done;
        invariant iter_end == 255u8;
        invariant 0 <= iter_done and iter_done <= 1;
        invariant iter_done != 0 implies total == 256u32;
        invariant total == iter_start + iter_done;
    }
}
