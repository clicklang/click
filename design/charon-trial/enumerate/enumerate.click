verifying "enumerate.rs";

// `for (i, x) in xs.iter().enumerate()` holds the slice iterator's state,
// `iter_cursor` and `iter_remaining`, and `iter_count`, the values it has
// yielded: each iteration yields index `iter_count` and the element at
// `iter_cursor`, then advances both.

fn last_index(bytes: &[u8]) -> usize {
    views bytes[0..bytes.len()];
    ensures bytes.len() != 0u64 implies result == bytes.len() - 1u64;
} by {
    step_until(loop(0));
    loop {
        decreases iter_remaining;
        views bytes[0..bytes.len()];
        invariant iter_remaining <= bytes.len();
        invariant iter_count == bytes.len() - iter_remaining;
        invariant iter_cursor == bytes + (bytes.len() - iter_remaining);
        invariant iter_count != 0u64 implies last == iter_count - 1u64;
        preserve by {
            mark iteration;
            have to_integer(bytes.len() - iter_remaining) < 18446744073709551615;
            step_until(back_edge());
            have to_integer(iter_remaining) == to_integer(at(iteration, iter_remaining)) - 1;
            have to_integer(bytes.len() - iter_remaining) == to_integer(bytes.len()) - to_integer(iter_remaining);
            have to_integer(bytes.len() - at(iteration, iter_remaining)) == to_integer(bytes.len()) - to_integer(at(iteration, iter_remaining));
            have to_integer((bytes.len() - at(iteration, iter_remaining)) + 1u64) == to_integer(bytes.len() - at(iteration, iter_remaining)) + 1;
            have to_integer(bytes.len() - iter_remaining) == to_integer((bytes.len() - at(iteration, iter_remaining)) + 1u64);
            have at(iteration, iter_cursor) + 1 == bytes + ((bytes.len() - at(iteration, iter_remaining)) + 1u64) by {
                solve() using {
                    at(iteration, iter_cursor) == bytes + at(iteration, (bytes.len() - iter_remaining));
                    at(iteration, to_integer(bytes.len() - iter_remaining) < 18446744073709551615);
                };
            }
            have iter_cursor == bytes + (bytes.len() - iter_remaining);
        }
    }
    have iter_remaining == 0u64;
    have iter_count == bytes.len();
}

// A reference pattern binds the element's address, read by `*word`.
fn last_pair(words: &[u16]) -> u32 {
    views words[0..words.len()];
    ensures result <= 65535u32;
} by {
    step_until(loop(0));
    loop {
        decreases iter_remaining;
        views words[0..words.len()];
        invariant iter_remaining <= words.len();
        invariant iter_count == words.len() - iter_remaining;
        invariant iter_cursor == words + (words.len() - iter_remaining);
        invariant iter_count != 0u64 implies index == iter_count - 1u64;
        invariant value <= 65535u32;
        preserve by {
            mark iteration;
            have to_integer(words.len() - iter_remaining) < 18446744073709551615;
            step_until(back_edge());
            have to_integer(iter_remaining) == to_integer(at(iteration, iter_remaining)) - 1;
            have to_integer(words.len() - iter_remaining) == to_integer(words.len()) - to_integer(iter_remaining);
            have to_integer(words.len() - at(iteration, iter_remaining)) == to_integer(words.len()) - to_integer(at(iteration, iter_remaining));
            have to_integer((words.len() - at(iteration, iter_remaining)) + 1u64) == to_integer(words.len() - at(iteration, iter_remaining)) + 1;
            have to_integer(words.len() - iter_remaining) == to_integer((words.len() - at(iteration, iter_remaining)) + 1u64);
            have at(iteration, iter_cursor) + 1 == words + ((words.len() - at(iteration, iter_remaining)) + 1u64) by {
                solve() using {
                    at(iteration, iter_cursor) == words + at(iteration, (words.len() - iter_remaining));
                    at(iteration, to_integer(words.len() - iter_remaining) < 18446744073709551615);
                };
            }
            have iter_cursor == words + (words.len() - iter_remaining);
        }
    }
}
