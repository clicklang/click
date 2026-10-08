verifying "chunks.rs";

fn cover(bytes: &[u8]) -> usize {
    requires bytes_len <= 1000u64;
    views bytes[0..(int32)(uint32)bytes_len];
    ensures result == bytes_len % 4u64;
    ensures forall (k: int32) {
        0 <= k and k < (int32)(uint32)bytes_len implies bytes[k] == old(bytes[k])
    };
} by {
    have bytes_len % 4u64 <= bytes_len by { normalize(); }
    have bytes_len - bytes_len % 4u64 <= bytes_len by { normalize() using { bytes_len % 4u64 <= bytes_len; } }
    have bytes_len - bytes_len % 4u64 <= 1000u64 by { normalize() using { bytes_len - bytes_len % 4u64 <= bytes_len; bytes_len <= 1000u64; } }
    have bytes_len - bytes_len % 4u64 <= 2147483647u64 by { normalize() using { bytes_len - bytes_len % 4u64 <= 1000u64; } }
    have 0 <= (int32)(uint32)(bytes_len - bytes_len % 4u64) by { normalize() using { bytes_len - bytes_len % 4u64 <= 2147483647u64; } }
    have ((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 1000 by { simp(); }
    have bytes_len <= 2147483647u64 by { normalize() using { bytes_len <= 1000u64; } }
    have ((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= (int32)(uint32)bytes_len by { normalize() using { bytes_len - bytes_len % 4u64 <= bytes_len; bytes_len <= 2147483647u64; } }
    execute_until(loop(0));
    have viewable(bytes[0..(int32)(uint32)bytes_len]) by {
        transport(at(function.entry, viewable(bytes[0..(int32)(uint32)bytes_len])), viewable(bytes[0..(int32)(uint32)bytes_len])) using {
            at(function.entry, viewable(bytes[0..(int32)(uint32)bytes_len]));
            0 <= (int32)(uint32)bytes_len;
        }
    }
    have bytes_len <= 2147483647u64 by { normalize() using { bytes_len <= 1000u64; } }
    have (((int32)(uint32)(bytes_len - bytes_len % 4u64)) % 4) == 0 by { normalize() using { bytes_len <= 2147483647u64; } }
    have iter_remaining == (int32)(uint32)(bytes_len - bytes_len % 4u64) by { simp(); }
    have iter_remaining % 4 == 0 by {
        rewrite(iter_remaining == (int32)(uint32)(bytes_len - bytes_len % 4u64)); simp();
    }
    loop {
        decreases iter_remaining;
        views bytes[0..(int32)(uint32)bytes_len];
        invariant viewable(bytes[0..(int32)(uint32)bytes_len]);
        invariant bytes_len <= 1000u64;
        invariant 0 <= (int32)(uint32)bytes_len and ((int32)(uint32)bytes_len) <= 1000;
        invariant 0 <= (int32)(uint32)(bytes_len - bytes_len % 4u64) and ((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= (int32)(uint32)bytes_len;
        invariant ((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 1000;
        invariant iter_size == 4u64;
        invariant iter_tail_len == bytes_len % 4u64;
        invariant tail_len == iter_tail_len;
        invariant iter_tail == bytes + (int32)(uint32)(bytes_len - bytes_len % 4u64);
        invariant tail == iter_tail;
        invariant 0 <= iter_remaining and iter_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64);
        invariant iter_remaining % 4 == 0;
        invariant iter_cursor == bytes + ((int32)(uint32)(bytes_len - bytes_len % 4u64) - iter_remaining);
        invariant 0 <= ((int32)(uint32)(bytes_len - bytes_len % 4u64) - iter_remaining) and ((int32)(uint32)(bytes_len - bytes_len % 4u64) - iter_remaining) <= 1000;
        preserve by {
            have 4 <= iter_remaining by { simp(); }
            mark iteration;
            have ((int32)(uint32)(bytes_len - bytes_len % 4u64) - iter_remaining) + 4 <= (int32)(uint32)bytes_len by {
                arithmetic() using {
                    4 <= iter_remaining;
                    iter_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64);
                    ((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= (int32)(uint32)bytes_len;
                    0 <= (int32)(uint32)bytes_len; ((int32)(uint32)bytes_len) <= 1000;
                    0 <= (int32)(uint32)(bytes_len - bytes_len % 4u64);
                }
            }
            execute_until(read(1)); step();
            have iter_remaining == at(iteration, iter_remaining) - 4 by { simp(); }
            have (at(iteration, iter_remaining) - 4) % 4 == at(iteration, iter_remaining % 4) by {
                normalize() using { at(iteration, 4 <= iter_remaining); }
            }
            have iter_remaining % 4 == 0 by {
                rewrite(iter_remaining == at(iteration, iter_remaining) - 4);
                rewrite((at(iteration, iter_remaining) - 4) % 4 == at(iteration, iter_remaining % 4)); simp();
            }
            have 0 <= iter_remaining by {
                arithmetic() using { iter_remaining == at(iteration, iter_remaining) - 4; at(iteration, 4 <= iter_remaining); }
            }
            have iter_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64) by {
                arithmetic() using {
                    iter_remaining == at(iteration, iter_remaining) - 4;
                    at(iteration, 4 <= iter_remaining);
                    at(iteration, iter_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64));
                    0 <= (int32)(uint32)(bytes_len - bytes_len % 4u64);
                    ((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 1000;
                }
            }
            have iter_cursor == at(iteration, iter_cursor) + 4 by { simp(); }
            have ((int32)(uint32)(bytes_len - bytes_len % 4u64) - iter_remaining) == at(iteration, (int32)(uint32)(bytes_len - bytes_len % 4u64) - iter_remaining) + 4 by {
                arithmetic() using {
                    iter_remaining == at(iteration, iter_remaining) - 4;
                    at(iteration, 4 <= iter_remaining);
                    at(iteration, iter_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64));
                    0 <= (int32)(uint32)(bytes_len - bytes_len % 4u64);
                    ((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 1000;
                }
            }
            have at(iteration, iter_cursor) + 4 == bytes + (at(iteration, (int32)(uint32)(bytes_len - bytes_len % 4u64) - iter_remaining) + 4) by {
                arithmetic() using {
                    at(iteration, iter_cursor == bytes + ((int32)(uint32)(bytes_len - bytes_len % 4u64) - iter_remaining));
                    at(iteration, 0 <= ((int32)(uint32)(bytes_len - bytes_len % 4u64) - iter_remaining));
                    at(iteration, ((int32)(uint32)(bytes_len - bytes_len % 4u64) - iter_remaining) <= 1000);
                }
            }
            have iter_cursor == bytes + ((int32)(uint32)(bytes_len - bytes_len % 4u64) - iter_remaining) by {
                rewrite(((int32)(uint32)(bytes_len - bytes_len % 4u64) - iter_remaining) == at(iteration, (int32)(uint32)(bytes_len - bytes_len % 4u64) - iter_remaining) + 4); simp();
            }
            execute_until(back_edge());
            # Transport after the body's automatic-storage cleanup.
            have viewable(bytes[0..(int32)(uint32)bytes_len]) by {
                transport(at(iteration, viewable(bytes[0..(int32)(uint32)bytes_len])), viewable(bytes[0..(int32)(uint32)bytes_len])) using {
                    at(iteration, viewable(bytes[0..(int32)(uint32)bytes_len]));
                    0 <= (int32)(uint32)bytes_len;
                }
            }
            close_invariants();
        }
    }
    have iter_remaining < 4 by {
        cases {
            not (0 < iter_remaining) => {
                have iter_remaining <= 0 by { simp(); }
                arithmetic() using { iter_remaining <= 0; }
            }
            not (4 <= iter_remaining) => { simp(); }
        }
    }
    have iter_remaining % 4 == iter_remaining by { normalize() using { 0 <= iter_remaining; iter_remaining < 4; } }
    have iter_remaining == 0 by { simp(); }
    have iter_cursor == iter_tail by { simp(); }
    execute();
    have forall (k: int32) {
        0 <= k and k < (int32)(uint32)bytes_len implies bytes[k] == old(bytes[k])
    } by { intro(); intro(); simp(); }
    simp();
}
