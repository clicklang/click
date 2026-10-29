verifying "slices.rs";

// A slice of any integer element, shared or mutable, is a pointer and a
// length, as a byte slice is: indexed reads and writes owe Rust's index
// panic check, the length is `xs.len()`, and a slice passes to a callee
// whole. Iteration keeps the shared slice iterator's cursor and remaining
// count, as `examples/rust-iterators` does for bytes.

fn first(xs: &[i32]) -> i32 {
    views *xs;
    ensures xs.len() == 0 implies result == 0;
    ensures xs.len() > 0 implies result == xs[0];
}

fn sum(xs: &[u32]) -> u32 {
    views *xs;
    ensures true;
} by {
    step_until(loop(0));
    loop {
        decreases xs.len() - i;
        invariant i <= xs.len();
    }
}

fn zero(xs: &mut [u64]) {
    owns *xs;
    ensures xs.len() == old(xs.len());
} by {
    step_until(loop(0));
    loop {
        decreases xs.len() - i;
        invariant i <= xs.len();
    }
}

fn set_at(xs: &mut [i64], k: usize, v: i64) {
    owns *xs;
    requires k < xs.len();
    ensures xs[k] == v;
}

fn get(xs: &[u16], k: usize) -> u16 {
    views *xs;
    requires k < xs.len();
    ensures result == xs[k];
}

fn swap_ends(xs: &mut [i8]) {
    owns *xs;
    ensures xs.len() >= 2 implies xs[0] == old(xs[xs.len() - 1]);
} by {
    if xs.len() >= 2 {
        have 0u64 < xs.len() - 1u64 by { solve(); }
        have xs.len() - 1u64 < xs.len() by { solve(); }
        step_until(function.exit);
        have xs[0] == old(xs[xs.len() - 1]) by {
            normalize() using {
                xs.len() >= 2;
                0u64 < xs.len() - 1u64;
                xs.len() - 1u64 < xs.len();
            };
        }
        solve();
    } else {
        step_until(function.exit);
        solve();
    }
}

fn last(xs: &[i64]) -> i64 {
    views xs[0..xs.len()];
    requires xs.len() <= 1000u64;
    ensures true;
} by {
    step_until(loop(0));
    loop {
        decreases iter_remaining;
        views xs[0..xs.len()];
        invariant xs.len() <= 1000u64;
        invariant iter_remaining <= xs.len();
        invariant iter_cursor == xs + (xs.len() - iter_remaining);
        preserve by {
            mark iteration;
            have to_integer(xs.len() - iter_remaining) < 18446744073709551615;
            step_until(back_edge());
            have to_integer(iter_remaining) == to_integer(at(iteration, iter_remaining)) - 1;
            have to_integer(xs.len() - iter_remaining) == to_integer(xs.len()) - to_integer(iter_remaining);
            have to_integer(xs.len() - at(iteration, iter_remaining)) == to_integer(xs.len()) - to_integer(at(iteration, iter_remaining));
            have to_integer((xs.len() - at(iteration, iter_remaining)) + 1u64) == to_integer(xs.len() - at(iteration, iter_remaining)) + 1;
            have to_integer(xs.len() - iter_remaining) == to_integer((xs.len() - at(iteration, iter_remaining)) + 1u64);
            have iter_remaining <= xs.len();
            have iter_remaining < at(iteration, iter_remaining);
            have at(iteration, iter_cursor) + 1 == xs + ((xs.len() - at(iteration, iter_remaining)) + 1u64) by {
                solve() using {
                    at(iteration, iter_cursor) == xs + at(iteration, (xs.len() - iter_remaining));
                    at(iteration, to_integer(xs.len() - iter_remaining) < 18446744073709551615);
                };
            }
            have iter_cursor == xs + (xs.len() - iter_remaining);
        }
    }
}

fn head(xs: &[u64]) -> u64 {
    views *xs;
    ensures xs.len() > 0 implies result == xs[0];
}

fn head_twice(xs: &[u64]) -> u64 {
    views *xs;
    ensures xs.len() > 0 implies result == xs[0];
}

fn clear_first(xs: &mut [i16]) {
    owns *xs;
    ensures xs.len() > 0 implies xs[0] == 0i16;
}

fn clear_twice(xs: &mut [i16]) {
    owns *xs;
    ensures xs.len() > 0 implies xs[0] == 0i16;
}
