verifying "chunks.rs";

fn cover(bytes: &[u8]) -> usize {
    requires bytes.len() <= 1000u64;
    views bytes[0..bytes.len()];
    ensures result == bytes.len() % 4u64;
    ensures forall (k: int32) {
        0 <= k and k < (int32)(uint32)bytes.len() implies bytes[k] == old(bytes[k])
    };
} by {
    have bytes.len() % 4u64 <= bytes.len() by { normalize(); }
    have bytes.len() - bytes.len() % 4u64 <= bytes.len() by { normalize() using { bytes.len() % 4u64 <= bytes.len(); } }
    have bytes.len() - bytes.len() % 4u64 <= 1000u64 by { normalize() using { bytes.len() - bytes.len() % 4u64 <= bytes.len(); bytes.len() <= 1000u64; } }
    have bytes.len() - bytes.len() % 4u64 <= 2147483647u64 by { normalize() using { bytes.len() - bytes.len() % 4u64 <= 1000u64; } }
    have 0 <= (int32)(uint32)(bytes.len() - bytes.len() % 4u64) by { normalize() using { bytes.len() - bytes.len() % 4u64 <= 2147483647u64; } }
    have ((int32)(uint32)(bytes.len() - bytes.len() % 4u64)) <= 1000 by { simp(); }
    have bytes.len() <= 2147483647u64 by { normalize() using { bytes.len() <= 1000u64; } }
    have ((int32)(uint32)(bytes.len() - bytes.len() % 4u64)) <= (int32)(uint32)bytes.len() by { normalize() using { bytes.len() - bytes.len() % 4u64 <= bytes.len(); bytes.len() <= 2147483647u64; } }
    execute_until(loop(0));
    have viewable(bytes[0..bytes.len()]) by {
        transport(at(function.entry, viewable(bytes[0..bytes.len()])), viewable(bytes[0..bytes.len()])) using {
            at(function.entry, viewable(bytes[0..bytes.len()]));
            0 <= (int32)(uint32)bytes.len();
        }
    }
    have bytes.len() <= 2147483647u64 by { normalize() using { bytes.len() <= 1000u64; } }
    have (((int32)(uint32)(bytes.len() - bytes.len() % 4u64)) % 4) == 0 by { normalize() using { bytes.len() <= 2147483647u64; } }
    have chunks_remaining == (int32)(uint32)(bytes.len() - bytes.len() % 4u64) by { simp(); }
    have chunks_remaining % 4 == 0 by {
        rewrite(chunks_remaining == (int32)(uint32)(bytes.len() - bytes.len() % 4u64)); simp();
    }
    loop {
        decreases chunks_remaining;
        views bytes[0..bytes.len()];
        invariant viewable(bytes[0..bytes.len()]);
        invariant bytes.len() <= 1000u64;
        invariant 0 <= (int32)(uint32)bytes.len() and ((int32)(uint32)bytes.len()) <= 1000;
        invariant 0 <= (int32)(uint32)(bytes.len() - bytes.len() % 4u64) and ((int32)(uint32)(bytes.len() - bytes.len() % 4u64)) <= (int32)(uint32)bytes.len();
        invariant ((int32)(uint32)(bytes.len() - bytes.len() % 4u64)) <= 1000;
        invariant chunks_size == 4u64;
        invariant chunks_tail_len == bytes.len() % 4u64;
        invariant tail_len == chunks_tail_len;
        invariant chunks_tail == bytes + (int32)(uint32)(bytes.len() - bytes.len() % 4u64);
        invariant tail == chunks_tail;
        invariant 0 <= chunks_remaining and chunks_remaining <= (int32)(uint32)(bytes.len() - bytes.len() % 4u64);
        invariant chunks_remaining % 4 == 0;
        invariant chunks_cursor == bytes + ((int32)(uint32)(bytes.len() - bytes.len() % 4u64) - chunks_remaining);
        invariant 0 <= ((int32)(uint32)(bytes.len() - bytes.len() % 4u64) - chunks_remaining) and ((int32)(uint32)(bytes.len() - bytes.len() % 4u64) - chunks_remaining) <= 1000;
        preserve by {
            have 4 <= chunks_remaining by { simp(); }
            mark iteration;
            have ((int32)(uint32)(bytes.len() - bytes.len() % 4u64) - chunks_remaining) + 4 <= (int32)(uint32)bytes.len() by {
                arithmetic() using {
                    4 <= chunks_remaining;
                    chunks_remaining <= (int32)(uint32)(bytes.len() - bytes.len() % 4u64);
                    ((int32)(uint32)(bytes.len() - bytes.len() % 4u64)) <= (int32)(uint32)bytes.len();
                    0 <= (int32)(uint32)bytes.len(); ((int32)(uint32)bytes.len()) <= 1000;
                    0 <= (int32)(uint32)(bytes.len() - bytes.len() % 4u64);
                }
            }
            execute_until(read(1)); step();
            have viewable(bytes[0..bytes.len()]) by {
                transport(at(iteration, viewable(bytes[0..bytes.len()])), viewable(bytes[0..bytes.len()])) using {
                    at(iteration, viewable(bytes[0..bytes.len()]));
                    0 <= (int32)(uint32)bytes.len();
                }
            }
            have chunks_remaining == at(iteration, chunks_remaining) - 4 by { simp(); }
            have (at(iteration, chunks_remaining) - 4) % 4 == at(iteration, chunks_remaining % 4) by {
                normalize() using { at(iteration, 4 <= chunks_remaining); }
            }
            have chunks_remaining % 4 == 0 by {
                rewrite(chunks_remaining == at(iteration, chunks_remaining) - 4);
                rewrite((at(iteration, chunks_remaining) - 4) % 4 == at(iteration, chunks_remaining % 4)); simp();
            }
            have 0 <= chunks_remaining by {
                arithmetic() using { chunks_remaining == at(iteration, chunks_remaining) - 4; at(iteration, 4 <= chunks_remaining); }
            }
            have chunks_remaining <= (int32)(uint32)(bytes.len() - bytes.len() % 4u64) by {
                arithmetic() using {
                    chunks_remaining == at(iteration, chunks_remaining) - 4;
                    at(iteration, 4 <= chunks_remaining);
                    at(iteration, chunks_remaining <= (int32)(uint32)(bytes.len() - bytes.len() % 4u64));
                    0 <= (int32)(uint32)(bytes.len() - bytes.len() % 4u64);
                    ((int32)(uint32)(bytes.len() - bytes.len() % 4u64)) <= 1000;
                }
            }
            have chunks_cursor == at(iteration, chunks_cursor) + 4 by { simp(); }
            have ((int32)(uint32)(bytes.len() - bytes.len() % 4u64) - chunks_remaining) == at(iteration, (int32)(uint32)(bytes.len() - bytes.len() % 4u64) - chunks_remaining) + 4 by {
                arithmetic() using {
                    chunks_remaining == at(iteration, chunks_remaining) - 4;
                    at(iteration, 4 <= chunks_remaining);
                    at(iteration, chunks_remaining <= (int32)(uint32)(bytes.len() - bytes.len() % 4u64));
                    0 <= (int32)(uint32)(bytes.len() - bytes.len() % 4u64);
                    ((int32)(uint32)(bytes.len() - bytes.len() % 4u64)) <= 1000;
                }
            }
            have at(iteration, chunks_cursor) + 4 == bytes + (at(iteration, (int32)(uint32)(bytes.len() - bytes.len() % 4u64) - chunks_remaining) + 4) by {
                arithmetic() using {
                    at(iteration, chunks_cursor == bytes + ((int32)(uint32)(bytes.len() - bytes.len() % 4u64) - chunks_remaining));
                    at(iteration, 0 <= ((int32)(uint32)(bytes.len() - bytes.len() % 4u64) - chunks_remaining));
                    at(iteration, ((int32)(uint32)(bytes.len() - bytes.len() % 4u64) - chunks_remaining) <= 1000);
                }
            }
            have chunks_cursor == bytes + ((int32)(uint32)(bytes.len() - bytes.len() % 4u64) - chunks_remaining) by {
                rewrite(((int32)(uint32)(bytes.len() - bytes.len() % 4u64) - chunks_remaining) == at(iteration, (int32)(uint32)(bytes.len() - bytes.len() % 4u64) - chunks_remaining) + 4); simp();
            }
            execute_until(back_edge());
            close_invariants();
        }
    }
    have chunks_remaining < 4 by {
        cases {
            not (0 < chunks_remaining) => {
                have chunks_remaining <= 0 by { simp(); }
                arithmetic() using { chunks_remaining <= 0; }
            }
            not (4 <= chunks_remaining) => { simp(); }
        }
    }
    have chunks_remaining % 4 == chunks_remaining by { normalize() using { 0 <= chunks_remaining; chunks_remaining < 4; } }
    have chunks_remaining == 0 by { simp(); }
    have chunks_cursor == chunks_tail by { simp(); }
    execute();
    have forall (k: int32) {
        0 <= k and k < (int32)(uint32)bytes.len() implies bytes[k] == old(bytes[k])
    } by { intro(); intro(); simp(); }
    simp();
}
