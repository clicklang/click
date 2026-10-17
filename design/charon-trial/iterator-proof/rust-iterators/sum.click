import click::integer;
import click::machine_integer;

verifying "sum.rs";
function prefix(bytes: &[u8], end: usize) -> Integer {
    (0..end).fold(0, |acc, k| {
        acc + to_integer(bytes[k] as i32)
    })
}
fn sum(bytes: &[u8]) -> i32 {
    requires bytes.len() <= 1000u64;
    views bytes[0..bytes.len()];
    ensures to_integer(result) == old(prefix(bytes, bytes.len()));
} by {
    execute_until(loop(0));
    have prefix(bytes, bytes.len() - iter_remaining) == 0 by {
        peel(prefix(bytes, bytes.len() - iter_remaining)) using {
            bytes.len() - iter_remaining <= 0u64;
        }; simp();
    }
    loop {
        decreases iter_remaining;
        views bytes[0..bytes.len()];
        invariant bytes.len() <= 1000u64;
        invariant iter_remaining <= bytes.len();
        invariant iter_cursor == bytes + (bytes.len() - iter_remaining);
        invariant 0 <= to_integer(total) and to_integer(total) <= 255 * to_integer(bytes.len() - iter_remaining);
        invariant to_integer(total) == prefix(bytes, bytes.len() - iter_remaining);
        preserve by {
            mark iteration;
            have bytes.len() - iter_remaining < bytes.len() by {
                arithmetic() using { 0u64 < iter_remaining; iter_remaining <= bytes.len(); };
            }
            have to_integer((bytes.len() - iter_remaining)) <= 1000 by auto();
            have (bytes.len() - iter_remaining) < 1000u64 by {
                apply(uint64_less_than_less_equal_transitive((bytes.len() - iter_remaining), bytes.len(), 1000u64)) using {
                    (bytes.len() - iter_remaining) < bytes.len();
                    bytes.len() <= 1000u64;
                };
            }
            have (bytes.len() - iter_remaining) < 18446744073709551615u64 by {
                apply(uint64_less_than_transitive((bytes.len() - iter_remaining), 1000u64, 18446744073709551615u64)) using {
                    (bytes.len() - iter_remaining) < 1000u64;
                    1000u64 < 18446744073709551615u64;
                };
            }
            have prefix(bytes, (bytes.len() - iter_remaining) + 1u64) == prefix(bytes, (bytes.len() - iter_remaining)) + to_integer(bytes[(bytes.len() - iter_remaining)] as i32) by {
                peel(prefix(bytes, (bytes.len() - iter_remaining) + 1u64)) using {
                    0u64 <= (bytes.len() - iter_remaining);
                    (bytes.len() - iter_remaining) < 18446744073709551615u64;
                };
                simp();
            }
            have to_integer((bytes.len() - iter_remaining)) + 1 <= 18446744073709551615 by {
                arithmetic() using { to_integer((bytes.len() - iter_remaining)) <= 1000; };
            }
            have to_integer((bytes.len() - iter_remaining) + 1u64) == to_integer((bytes.len() - iter_remaining)) + 1 by {
                apply(uint64_add_to_integer((bytes.len() - iter_remaining), 1u64)) using {
                    to_integer((bytes.len() - iter_remaining)) + 1 <= 18446744073709551615;
                };
            }
            execute_until(read(0));
            step();
            mark loaded;
            have at(iteration, bytes[(bytes.len() - iter_remaining)]) == byte;
            have 0 <= to_integer(byte as i32) by {
                apply(int32_less_equal_to_integer(0, byte as i32)) using { 0 <= byte as i32; };
            }
            have to_integer(byte as i32) <= 255 by {
                apply(int32_less_equal_to_integer(byte as i32, 255)) using { 255 >= byte as i32; };
            }
            have defined(total + byte as i32) by auto();
            have to_integer(total + byte as i32) == to_integer(total) + to_integer(byte as i32) by {
                apply(int32_add_to_integer(total, byte as i32)) using { defined(total + byte as i32); };
            }
            have 0 <= to_integer(total + byte as i32) by {
                arithmetic() using {
                    0 <= to_integer(total);
                    0 <= to_integer(byte as i32);
                    to_integer(total + byte as i32) == to_integer(total) + to_integer(byte as i32);
                };
            }
            have to_integer(total + byte as i32) <= 255 * at(iteration, to_integer((bytes.len() - iter_remaining) + 1u64)) by {
                arithmetic() using {
                    at(iteration, to_integer(total) <= 255 * to_integer((bytes.len() - iter_remaining)));
                    to_integer(byte as i32) <= 255;
                    to_integer(total + byte as i32) == to_integer(total) + to_integer(byte as i32);
                    at(iteration, to_integer((bytes.len() - iter_remaining) + 1u64) == to_integer((bytes.len() - iter_remaining)) + 1);
                };
            }
            have (bytes.len() - iter_remaining) == (bytes.len() - at(iteration, iter_remaining)) + 1u64 by {
                arithmetic() using {
                    iter_remaining == at(iteration, iter_remaining) - 1u64;
                    0u64 < at(iteration, iter_remaining);
                    at(iteration, iter_remaining) <= bytes.len();
                };
            }
            mark addition;
            execute_until(assignment(total, 1)); step();
            execute_until(back_edge());
            have iter_remaining <= bytes.len() by {
                arithmetic() using {
                    iter_remaining == at(iteration, iter_remaining) - 1u64;
                    0u64 < at(iteration, iter_remaining);
                    at(iteration, iter_remaining) <= bytes.len();
                };
            }
            have at(iteration, iter_cursor) + 1 == bytes + ((bytes.len() - at(iteration, iter_remaining)) + 1u64) by {
                arithmetic() using {
                    at(iteration, iter_cursor) == bytes + at(iteration, (bytes.len() - iter_remaining));
                    at(iteration, (bytes.len() - iter_remaining)) < 18446744073709551615u64;
                };
            }
            have iter_remaining < at(iteration, iter_remaining) by {
                arithmetic() using {
                    iter_remaining == at(iteration, iter_remaining) - 1u64;
                    0u64 < at(iteration, iter_remaining);
                };
            }
        }
    }
    have iter_remaining == 0u64 by {
        arithmetic() using { not 0u64 < iter_remaining; };
    }
    have (bytes.len() - iter_remaining) == bytes.len() by auto();
    execute();
    simp();
}
