verifying "sum.rs";
function prefix(bytes: const uint8*, end: uint64) -> Integer {
    (0..end).fold(0, |acc, k| {
        acc + to_integer((int32)bytes[k])
    })
}
fn sum(bytes: &[u8]) -> i32 {
    requires bytes.len() <= 1000u64;
    views bytes[0..bytes.len()];
    ensures to_integer(result) == old(prefix(bytes, bytes.len()));
} by {
    execute_until(loop(0));
    have iter_remaining == bytes.len() by { simp(); }
    have bytes.len() - iter_remaining == 0u64 by {
        rewrite(iter_remaining == bytes.len()); simp();
    }
    have prefix(bytes, bytes.len() - iter_remaining) == 0 by {
        peel(prefix(bytes, bytes.len() - iter_remaining)) using {
            bytes.len() - iter_remaining <= 0u64;
        } simp();
    }
    have to_integer(total) == 0 by {
        simp();
    }
    have to_integer(total) == prefix(bytes, bytes.len() - iter_remaining) by {
        arithmetic() using {
            to_integer(total) == 0;
            prefix(bytes, bytes.len() - iter_remaining) == 0;
        }
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
            have 0u64 < iter_remaining by { simp(); }
            have bytes.len() - iter_remaining < bytes.len() by {
                arithmetic() using { 0u64 < iter_remaining; iter_remaining <= bytes.len(); }
            }
            have to_integer((bytes.len() - iter_remaining)) < to_integer(bytes.len()) by {
                apply(uint64_less_than_to_integer((bytes.len() - iter_remaining), bytes.len())) using { (bytes.len() - iter_remaining) < bytes.len(); }
            }
            have to_integer(bytes.len()) <= 1000 by {
                apply(uint64_less_equal_to_integer(bytes.len(), 1000u64)) using { bytes.len() <= 1000u64; }
            }
            have to_integer((bytes.len() - iter_remaining)) <= 1000 by {
                arithmetic() using {
                    to_integer((bytes.len() - iter_remaining)) < to_integer(bytes.len());
                    to_integer(bytes.len()) <= 1000;
                }
            }
            have to_integer(total) <= 255000 by {
                arithmetic() using {
                    to_integer(total) <= 255 * to_integer((bytes.len() - iter_remaining));
                    to_integer((bytes.len() - iter_remaining)) <= 1000;
                }
            }
            have (bytes.len() - iter_remaining) < 1000u64 by {
                apply(uint64_lt_le_transitive((bytes.len() - iter_remaining), bytes.len(), 1000u64)) using {
                    (bytes.len() - iter_remaining) < bytes.len();
                    bytes.len() <= 1000u64;
                }
            }
            have (bytes.len() - iter_remaining) < 18446744073709551615u64 by {
                apply(uint64_lt_transitive((bytes.len() - iter_remaining), 1000u64, 18446744073709551615u64)) using {
                    (bytes.len() - iter_remaining) < 1000u64;
                    1000u64 < 18446744073709551615u64;
                }
            }
            have defined(bytes[(bytes.len() - iter_remaining)]) by {
                transport(at(function.entry, viewable(bytes[0..bytes.len()])), defined(bytes[(bytes.len() - iter_remaining)])) using {
                    at(function.entry, viewable(bytes[0..bytes.len()]));
                    (bytes.len() - iter_remaining) < bytes.len();
                    bytes.len() <= 9223372036854775807u64;
                }
            }
            have prefix(bytes, (bytes.len() - iter_remaining) + 1u64) == prefix(bytes, (bytes.len() - iter_remaining)) + to_integer((int32)bytes[(bytes.len() - iter_remaining)]) by {
                peel(prefix(bytes, (bytes.len() - iter_remaining) + 1u64)) using {
                    0u64 <= (bytes.len() - iter_remaining);
                    (bytes.len() - iter_remaining) < 18446744073709551615u64;
                }
                simp();
            }
            have to_integer((bytes.len() - iter_remaining)) + 1 <= 18446744073709551615 by {
                arithmetic() using { to_integer((bytes.len() - iter_remaining)) <= 1000; }
            }
            have to_integer((bytes.len() - iter_remaining) + 1u64) == to_integer((bytes.len() - iter_remaining)) + 1 by {
                apply(uint64_add_to_integer((bytes.len() - iter_remaining), 1u64)) using {
                    to_integer((bytes.len() - iter_remaining)) + 1 <= 18446744073709551615;
                }
            }
            execute_until(read(0));
            let loaded_byte = step();
            mark loaded;
            have 0 <= (int32)loaded_byte and 255 >= (int32)loaded_byte by { simp(); }
            have at(iteration, bytes[(bytes.len() - iter_remaining)]) == loaded_byte by { simp(); }
            have at(iteration, to_integer((int32)bytes[(bytes.len() - iter_remaining)])) == to_integer((int32)loaded_byte) by {
                rewrite(at(iteration, bytes[(bytes.len() - iter_remaining)]) == loaded_byte);
                normalize();
            }
            have 0 <= to_integer((int32)loaded_byte) by {
                apply(int32_less_equal_to_integer(0, (int32)loaded_byte)) using { 0 <= (int32)loaded_byte; }
            }
            have to_integer((int32)loaded_byte) <= 255 by {
                apply(int32_less_equal_to_integer((int32)loaded_byte, 255)) using { 255 >= (int32)loaded_byte; }
            }
            have to_integer(total) + to_integer((int32)loaded_byte) >= -2147483648 by {
                arithmetic() using { 0 <= to_integer(total); 0 <= to_integer((int32)loaded_byte); }
            }
            have to_integer(total) + to_integer((int32)loaded_byte) <= 2147483647 by {
                arithmetic() using { to_integer(total) <= 255000; to_integer((int32)loaded_byte) <= 255; }
            }
            have defined(total + (int32)loaded_byte) by {
                apply(int32_add_defined_by_integer_bounds(total, (int32)loaded_byte)) using {
                    to_integer(total) + to_integer((int32)loaded_byte) >= -2147483648;
                    to_integer(total) + to_integer((int32)loaded_byte) <= 2147483647;
                } simp();
            }
            have to_integer(total + (int32)loaded_byte) == to_integer(total) + to_integer((int32)loaded_byte) by {
                apply(int32_add_to_integer(total, (int32)loaded_byte)) using { defined(total + (int32)loaded_byte); }
            }
            have to_integer(total + (int32)loaded_byte) == at(iteration, prefix(bytes, (bytes.len() - iter_remaining) + 1u64)) by {
                arithmetic() using {
                    to_integer(total + (int32)loaded_byte) == to_integer(total) + to_integer((int32)loaded_byte);
                    at(iteration, to_integer(total) == prefix(bytes, (bytes.len() - iter_remaining)));
                    at(iteration, prefix(bytes, (bytes.len() - iter_remaining) + 1u64) == prefix(bytes, (bytes.len() - iter_remaining)) + to_integer((int32)bytes[(bytes.len() - iter_remaining)]));
                    at(iteration, to_integer((int32)bytes[(bytes.len() - iter_remaining)])) == to_integer((int32)loaded_byte);
                }
            }
            have 0 <= to_integer(total + (int32)loaded_byte) by {
                arithmetic() using {
                    0 <= to_integer(total);
                    0 <= to_integer((int32)loaded_byte);
                    to_integer(total + (int32)loaded_byte) == to_integer(total) + to_integer((int32)loaded_byte);
                }
            }
            have to_integer(total + (int32)loaded_byte) <= 255 * at(iteration, to_integer((bytes.len() - iter_remaining) + 1u64)) by {
                arithmetic() using {
                    at(iteration, to_integer(total) <= 255 * to_integer((bytes.len() - iter_remaining)));
                    to_integer((int32)loaded_byte) <= 255;
                    to_integer(total + (int32)loaded_byte) == to_integer(total) + to_integer((int32)loaded_byte);
                    at(iteration, to_integer((bytes.len() - iter_remaining) + 1u64) == to_integer((bytes.len() - iter_remaining)) + 1);
                }
            }
            have (bytes.len() - iter_remaining) == (bytes.len() - at(iteration, iter_remaining)) + 1u64 by {
                arithmetic() using {
                    iter_remaining == at(iteration, iter_remaining) - 1u64;
                    0u64 < at(iteration, iter_remaining);
                    at(iteration, iter_remaining) <= bytes.len();
                }
            }
            mark addition;
            execute_until(assignment(total, 1)); step();
            have to_integer(total) == at(addition, to_integer(total + (int32)loaded_byte)) by { simp(); }
            execute_until(back_edge());
            have iter_remaining <= bytes.len() by {
                arithmetic() using {
                    iter_remaining == at(iteration, iter_remaining) - 1u64;
                    0u64 < at(iteration, iter_remaining);
                    at(iteration, iter_remaining) <= bytes.len();
                }
            }
            have at(iteration, iter_cursor) + 1 == bytes + ((bytes.len() - at(iteration, iter_remaining)) + 1u64) by {
                arithmetic() using {
                    at(iteration, iter_cursor) == bytes + at(iteration, (bytes.len() - iter_remaining));
                    at(iteration, (bytes.len() - iter_remaining)) < 18446744073709551615u64;
                }
            }
            have iter_cursor == bytes + (bytes.len() - iter_remaining) by {
                rewrite((bytes.len() - iter_remaining) == (bytes.len() - at(iteration, iter_remaining)) + 1u64);
                simp();
            }
            have 0 <= to_integer(total) by {
                arithmetic() using {
                    to_integer(total) == at(addition, to_integer(total + (int32)loaded_byte));
                    at(addition, 0 <= to_integer(total + (int32)loaded_byte));
                }
            }
            have to_integer((bytes.len() - iter_remaining)) == at(iteration, to_integer((bytes.len() - iter_remaining) + 1u64)) by {
                rewrite((bytes.len() - iter_remaining) == (bytes.len() - at(iteration, iter_remaining)) + 1u64);
                normalize();
            }
            have to_integer(total) <= 255 * to_integer((bytes.len() - iter_remaining)) by {
                arithmetic() using {
                    to_integer(total) == at(addition, to_integer(total + (int32)loaded_byte));
                    at(addition, to_integer(total + (int32)loaded_byte)) <= 255 * at(iteration, to_integer((bytes.len() - iter_remaining) + 1u64));
                    to_integer((bytes.len() - iter_remaining)) == at(iteration, to_integer((bytes.len() - iter_remaining) + 1u64));
                }
            }
            have prefix(bytes, (bytes.len() - iter_remaining)) == at(iteration, prefix(bytes, (bytes.len() - iter_remaining) + 1u64)) by {
                rewrite((bytes.len() - iter_remaining) == (bytes.len() - at(iteration, iter_remaining)) + 1u64);
                simp();
            }
            have to_integer(total) == prefix(bytes, (bytes.len() - iter_remaining)) by {
                arithmetic() using {
                    to_integer(total) == at(addition, to_integer(total + (int32)loaded_byte));
                    at(addition, to_integer(total + (int32)loaded_byte)) == at(iteration, prefix(bytes, (bytes.len() - iter_remaining) + 1u64));
                    prefix(bytes, (bytes.len() - iter_remaining)) == at(iteration, prefix(bytes, (bytes.len() - iter_remaining) + 1u64));
                }
            }
            have iter_remaining < at(iteration, iter_remaining) by {
                arithmetic() using {
                    iter_remaining == at(iteration, iter_remaining) - 1u64;
                    0u64 < at(iteration, iter_remaining);
                }
            }
            close_invariants();
        }
    }
    have iter_remaining == 0u64 by {
        arithmetic() using { not 0u64 < iter_remaining; }
    }
    have (bytes.len() - iter_remaining) == bytes.len() by {
        rewrite(iter_remaining == 0u64);
        simp();
    }
    have prefix(bytes, (bytes.len() - iter_remaining)) == prefix(bytes, bytes.len()) by {
        rewrite((bytes.len() - iter_remaining) == bytes.len());
        simp();
    }
    have to_integer(total) == prefix(bytes, bytes.len()) by {
        arithmetic() using {
            to_integer(total) == prefix(bytes, (bytes.len() - iter_remaining));
            prefix(bytes, (bytes.len() - iter_remaining)) == prefix(bytes, bytes.len());
        }
    }
    execute();
    simp();
}
