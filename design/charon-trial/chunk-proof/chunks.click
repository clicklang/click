import click::integer;

verifying "chunks.rs";

fn cover(bytes: &[u8]) -> usize {
    views bytes[0..bytes.len()];
    ensures result == bytes.len() % 4u64;
    ensures forall (k: usize) {
        k < bytes.len() implies bytes[k] == old(bytes[k])
    };
} by {
    have to_integer(bytes.len() % 4u64) <= to_integer(bytes.len()) by normalize();
    step_until(loop(0));
    have to_integer(iter_remaining) == to_integer(bytes.len() - bytes.len() % 4u64);
    have to_integer((bytes.len() - bytes.len() % 4u64) % 4u64) == to_integer(0u64);
    have to_integer(iter_remaining % 4u64) == to_integer(0u64) by {
        rewrite(to_integer(iter_remaining) == to_integer(bytes.len() - bytes.len() % 4u64)); solve();
    }
    have to_integer((bytes.len() - bytes.len() % 4u64) - iter_remaining) == to_integer(0u64);
    have iter_cursor == bytes + ((bytes.len() - bytes.len() % 4u64) - iter_remaining) by {
        rewrite(to_integer((bytes.len() - bytes.len() % 4u64) - iter_remaining) == to_integer(0u64)); solve();
    }
    loop {
        decreases iter_remaining;
        views bytes[0..bytes.len()];
        invariant iter_size == 4u64;
        invariant iter_tail_len == bytes.len() % 4u64;
        invariant tail_len == iter_tail_len;
        invariant iter_tail == bytes + (bytes.len() - bytes.len() % 4u64);
        invariant tail == iter_tail;
        invariant to_integer(iter_remaining) <= to_integer(bytes.len() - bytes.len() % 4u64);
        invariant to_integer(iter_remaining % 4u64) == to_integer(0u64);
        invariant iter_cursor == bytes + ((bytes.len() - bytes.len() % 4u64) - iter_remaining);
        preserve by {
            have 4u64 <= iter_remaining;
            mark iteration;
            have to_integer((bytes.len() - bytes.len() % 4u64) - iter_remaining) < to_integer(bytes.len());
            have to_integer(((bytes.len() - bytes.len() % 4u64) - iter_remaining) + 3u64) < to_integer(bytes.len());
            have 4 + to_integer((bytes.len() - bytes.len() % 4u64) - iter_remaining) <= to_integer(bytes.len());
            have 3 + to_integer((bytes.len() - bytes.len() % 4u64) - iter_remaining) <= to_integer(bytes.len());
            have 3 + to_integer((bytes.len() - bytes.len() % 4u64) - iter_remaining) < to_integer(bytes.len());
            step_until(read(1)); step();
            have to_integer(iter_remaining) == to_integer(at(iteration, iter_remaining) - 4u64);
            have to_integer((at(iteration, iter_remaining) - 4u64) % 4u64) == to_integer(at(iteration, iter_remaining % 4u64)) by {
                normalize() using { 4u64 <= at(iteration, iter_remaining); };
            }
            have to_integer(iter_remaining % 4u64) == to_integer(0u64) by {
                rewrite(to_integer(iter_remaining) == to_integer(at(iteration, iter_remaining) - 4u64));
                rewrite(to_integer((at(iteration, iter_remaining) - 4u64) % 4u64) == to_integer(at(iteration, iter_remaining % 4u64)));
                solve();
            }
            have to_integer(iter_remaining) <= to_integer((bytes.len() - bytes.len() % 4u64));
            have to_integer((bytes.len() - bytes.len() % 4u64) - at(iteration, iter_remaining)) <= to_integer(18446744073709551611u64);
            have at(iteration, iter_cursor) == bytes + ((bytes.len() - bytes.len() % 4u64) - at(iteration, iter_remaining));
            have at(iteration, iter_cursor) + 4 == bytes + (((bytes.len() - bytes.len() % 4u64) - at(iteration, iter_remaining)) + 4u64) by {
                solve() using {
                    at(iteration, iter_cursor) == bytes + ((bytes.len() - bytes.len() % 4u64) - at(iteration, iter_remaining));
                    to_integer((bytes.len() - bytes.len() % 4u64) - at(iteration, iter_remaining)) <= to_integer(18446744073709551611u64);
                };
            }
            have to_integer((bytes.len() - bytes.len() % 4u64) - iter_remaining) == to_integer(((bytes.len() - bytes.len() % 4u64) - at(iteration, iter_remaining)) + 4u64);
            have iter_cursor == bytes + ((bytes.len() - bytes.len() % 4u64) - iter_remaining) by {
                rewrite(to_integer((bytes.len() - bytes.len() % 4u64) - iter_remaining) == to_integer(((bytes.len() - bytes.len() % 4u64) - at(iteration, iter_remaining)) + 4u64));
                solve();
            }
            have iter_remaining < at(iteration, iter_remaining);
        }
    }
    have iter_remaining < 4u64 by {
        cases {
            not (0u64 < iter_remaining) => {
                solve() using { not 0u64 < iter_remaining; };
            }
            not (4u64 <= iter_remaining) => { assumption(); }
        }
    }
    have to_integer(iter_remaining % 4u64) == to_integer(iter_remaining) by {
        normalize() using { iter_remaining < 4u64; };
    }
    have iter_remaining == 0u64;
    have iter_cursor == iter_tail;
    step_until(function.exit);
    have forall (k: usize) {
        k < bytes.len() implies bytes[k] == old(bytes[k])
    } by { intro(); intro(); solve(); }
    solve();
}
