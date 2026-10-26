verifying "sum.rs";
function prefix(bytes: &[u8], end: usize) -> Integer {
    (0..end).fold(0, |acc, k| {
        acc + to_integer(bytes[k] as i32)
    })
}
fn sum(bytes: &[u8]) -> i32 {
    requires bytes.len() <= 1000u64;
    views bytes[0..bytes.len()];
    ensures result == old(prefix(bytes, bytes.len()));
} by {
    step_until(loop(0));
    have prefix(bytes, bytes.len() - iter_remaining) == 0 by {
        peel(prefix(bytes, bytes.len() - iter_remaining)) using {
            to_integer(bytes.len() - iter_remaining) <= 0;
        }; solve();
    }
    loop {
        decreases iter_remaining;
        views bytes[0..bytes.len()];
        invariant bytes.len() <= 1000u64;
        invariant iter_remaining <= bytes.len();
        invariant iter_cursor == bytes + (bytes.len() - iter_remaining);
        invariant 0 <= total and total <= 255 * (bytes.len() - iter_remaining);
        invariant total == prefix(bytes, bytes.len() - iter_remaining);
        preserve by {
            mark iteration;
            have 0 <= to_integer(bytes.len() - iter_remaining);
            have to_integer(bytes.len() - iter_remaining) < 18446744073709551615;
            have prefix(bytes, (bytes.len() - iter_remaining) + 1u64) == prefix(bytes, (bytes.len() - iter_remaining)) + to_integer(bytes[(bytes.len() - iter_remaining)] as i32) by {
                peel(prefix(bytes, (bytes.len() - iter_remaining) + 1u64)) using {
                    0 <= to_integer(bytes.len() - iter_remaining);
                    to_integer(bytes.len() - iter_remaining) < 18446744073709551615;
                };
                solve();
            }
            step_until(read(0));
            step();
            have at(iteration, bytes[(bytes.len() - iter_remaining)]) == byte;
            have defined(total + byte as i32);
            have to_integer(total + byte as i32) == to_integer(total) + to_integer(byte as i32);
            step_until(assignment(total, 1)); step();
            step_until(back_edge());
            have to_integer(iter_remaining) == to_integer(at(iteration, iter_remaining)) - 1;
            have to_integer(bytes.len() - iter_remaining) == to_integer(bytes.len()) - to_integer(iter_remaining);
            have to_integer(bytes.len() - at(iteration, iter_remaining)) == to_integer(bytes.len()) - to_integer(at(iteration, iter_remaining));
            have to_integer((bytes.len() - at(iteration, iter_remaining)) + 1u64) == to_integer(bytes.len() - at(iteration, iter_remaining)) + 1;
            have to_integer(bytes.len() - iter_remaining) == to_integer((bytes.len() - at(iteration, iter_remaining)) + 1u64);
            have iter_remaining <= bytes.len();
            have iter_remaining < at(iteration, iter_remaining);
            have at(iteration, iter_cursor) + 1 == bytes + ((bytes.len() - at(iteration, iter_remaining)) + 1u64) by {
                solve() using {
                    at(iteration, iter_cursor) == bytes + at(iteration, (bytes.len() - iter_remaining));
                    at(iteration, to_integer(bytes.len() - iter_remaining) < 18446744073709551615);
                };
            }
            have iter_cursor == bytes + (bytes.len() - iter_remaining);
            have 0 <= total;
            have to_integer(total) <= 255 * (bytes.len() - iter_remaining);
        }
    }
    have iter_remaining == 0u64;
    have prefix(bytes, bytes.len() - iter_remaining) == prefix(bytes, bytes.len()) by {
        rewrite(iter_remaining == 0u64);
        solve();
    }
    execute();
}
