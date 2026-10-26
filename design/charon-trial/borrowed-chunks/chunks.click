verifying "chunks.rs";

fn cover(bytes: &[u8]) -> usize {
    requires bytes.len() <= 1000u64;
    views bytes[0..bytes.len()];
    ensures result == bytes.len() % 4u64;
    ensures forall (k: int32) {
        0 <= k and k < bytes.len() as uint32 as int32 implies bytes[k] == old(bytes[k])
    };
} by {
    have bytes.len() % 4u64 <= bytes.len() by normalize();
    have bytes.len() - bytes.len() % 4u64 <= bytes.len() by { normalize() using { bytes.len() % 4u64 <= bytes.len(); }; }
    have bytes.len() - bytes.len() % 4u64 <= 1000u64 by { normalize() using { bytes.len() - bytes.len() % 4u64 <= bytes.len(); bytes.len() <= 1000u64; }; }
    have bytes.len() - bytes.len() % 4u64 <= 2147483647u64 by { normalize() using { bytes.len() - bytes.len() % 4u64 <= 1000u64; }; }
    have 0 <= (bytes.len() - bytes.len() % 4u64) as uint32 as int32 by { normalize() using { bytes.len() - bytes.len() % 4u64 <= 2147483647u64; }; }
    have ((bytes.len() - bytes.len() % 4u64) as uint32 as int32) <= 1000;
    have bytes.len() <= 2147483647u64 by { normalize() using { bytes.len() <= 1000u64; }; }
    have ((bytes.len() - bytes.len() % 4u64) as uint32 as int32) <= bytes.len() as uint32 as int32 by { normalize() using { bytes.len() - bytes.len() % 4u64 <= bytes.len(); bytes.len() <= 2147483647u64; }; }
    step_until(loop(0));
    have viewable(bytes[0..bytes.len()]) by {
        transport(at(function.entry, viewable(bytes[0..bytes.len()])), viewable(bytes[0..bytes.len()])) using {
            at(function.entry, viewable(bytes[0..bytes.len()]));
            0 <= bytes.len() as uint32 as int32;
        };
    }
    have bytes.len() <= 2147483647u64 by { normalize() using { bytes.len() <= 1000u64; }; }
    have (((bytes.len() - bytes.len() % 4u64) as uint32 as int32) % 4) == 0 by { normalize() using { bytes.len() <= 2147483647u64; }; }
    have chunks_remaining == (bytes.len() - bytes.len() % 4u64) as uint32 as int32;
    have chunks_remaining % 4 == 0 by {
        rewrite(chunks_remaining == (bytes.len() - bytes.len() % 4u64) as uint32 as int32); solve();
    }
    loop {
        decreases chunks_remaining;
        views bytes[0..bytes.len()];
        invariant viewable(bytes[0..bytes.len()]);
        invariant bytes.len() <= 1000u64;
        invariant 0 <= bytes.len() as uint32 as int32 and (bytes.len() as uint32 as int32) <= 1000;
        invariant 0 <= (bytes.len() - bytes.len() % 4u64) as uint32 as int32 and ((bytes.len() - bytes.len() % 4u64) as uint32 as int32) <= bytes.len() as uint32 as int32;
        invariant ((bytes.len() - bytes.len() % 4u64) as uint32 as int32) <= 1000;
        invariant chunks_size == 4u64;
        invariant chunks_tail_len == bytes.len() % 4u64;
        invariant tail_len == chunks_tail_len;
        invariant chunks_tail == bytes + (bytes.len() - bytes.len() % 4u64) as uint32 as int32;
        invariant tail == chunks_tail;
        invariant 0 <= chunks_remaining and chunks_remaining <= (bytes.len() - bytes.len() % 4u64) as uint32 as int32;
        invariant chunks_remaining % 4 == 0;
        invariant chunks_cursor == bytes + ((bytes.len() - bytes.len() % 4u64) as uint32 as int32 - chunks_remaining);
        invariant 0 <= ((bytes.len() - bytes.len() % 4u64) as uint32 as int32 - chunks_remaining) and ((bytes.len() - bytes.len() % 4u64) as uint32 as int32 - chunks_remaining) <= 1000;
        preserve by {
            have 4 <= chunks_remaining;
            mark iteration;
            have ((bytes.len() - bytes.len() % 4u64) as uint32 as int32 - chunks_remaining) + 4 <= bytes.len() as uint32 as int32 by {
                solve() using {
                    4 <= chunks_remaining;
                    chunks_remaining <= (bytes.len() - bytes.len() % 4u64) as uint32 as int32;
                    ((bytes.len() - bytes.len() % 4u64) as uint32 as int32) <= bytes.len() as uint32 as int32;
                    0 <= bytes.len() as uint32 as int32; (bytes.len() as uint32 as int32) <= 1000;
                    0 <= (bytes.len() - bytes.len() % 4u64) as uint32 as int32;
                };
            }
            step_until(read(1)); step();
            have viewable(bytes[0..bytes.len()]) by {
                transport(at(iteration, viewable(bytes[0..bytes.len()])), viewable(bytes[0..bytes.len()])) using {
                    at(iteration, viewable(bytes[0..bytes.len()]));
                    0 <= bytes.len() as uint32 as int32;
                };
            }
            have chunks_remaining == at(iteration, chunks_remaining) - 4;
            have (at(iteration, chunks_remaining) - 4) % 4 == at(iteration, chunks_remaining % 4) by {
                normalize() using { at(iteration, 4 <= chunks_remaining); };
            }
            have chunks_remaining % 4 == 0 by {
                rewrite(chunks_remaining == at(iteration, chunks_remaining) - 4);
                rewrite((at(iteration, chunks_remaining) - 4) % 4 == at(iteration, chunks_remaining % 4)); solve();
            }
            have 0 <= chunks_remaining by {
                solve() using { chunks_remaining == at(iteration, chunks_remaining) - 4; at(iteration, 4 <= chunks_remaining); };
            }
            have chunks_remaining <= (bytes.len() - bytes.len() % 4u64) as uint32 as int32 by {
                solve() using {
                    chunks_remaining == at(iteration, chunks_remaining) - 4;
                    at(iteration, 4 <= chunks_remaining);
                    at(iteration, chunks_remaining <= (bytes.len() - bytes.len() % 4u64) as uint32 as int32);
                    0 <= (bytes.len() - bytes.len() % 4u64) as uint32 as int32;
                    ((bytes.len() - bytes.len() % 4u64) as uint32 as int32) <= 1000;
                };
            }
            have chunks_cursor == at(iteration, chunks_cursor) + 4;
            have ((bytes.len() - bytes.len() % 4u64) as uint32 as int32 - chunks_remaining) == at(iteration, (bytes.len() - bytes.len() % 4u64) as uint32 as int32 - chunks_remaining) + 4 by {
                solve() using {
                    chunks_remaining == at(iteration, chunks_remaining) - 4;
                    at(iteration, 4 <= chunks_remaining);
                    at(iteration, chunks_remaining <= (bytes.len() - bytes.len() % 4u64) as uint32 as int32);
                    0 <= (bytes.len() - bytes.len() % 4u64) as uint32 as int32;
                    ((bytes.len() - bytes.len() % 4u64) as uint32 as int32) <= 1000;
                };
            }
            have at(iteration, chunks_cursor) + 4 == bytes + (at(iteration, (bytes.len() - bytes.len() % 4u64) as uint32 as int32 - chunks_remaining) + 4) by {
                solve() using {
                    at(iteration, chunks_cursor == bytes + ((bytes.len() - bytes.len() % 4u64) as uint32 as int32 - chunks_remaining));
                    at(iteration, 0 <= ((bytes.len() - bytes.len() % 4u64) as uint32 as int32 - chunks_remaining));
                    at(iteration, ((bytes.len() - bytes.len() % 4u64) as uint32 as int32 - chunks_remaining) <= 1000);
                };
            }
            have chunks_cursor == bytes + ((bytes.len() - bytes.len() % 4u64) as uint32 as int32 - chunks_remaining) by {
                rewrite(((bytes.len() - bytes.len() % 4u64) as uint32 as int32 - chunks_remaining) == at(iteration, (bytes.len() - bytes.len() % 4u64) as uint32 as int32 - chunks_remaining) + 4); solve();
            }
            step_until(back_edge());
            close_invariants();
        }
    }
    have chunks_remaining < 4 by {
        cases {
            not (0 < chunks_remaining) => {
                have chunks_remaining <= 0;
                solve() using { chunks_remaining <= 0; };
            }
            not (4 <= chunks_remaining) => { solve(); }
        }
    }
    have chunks_remaining % 4 == chunks_remaining by { normalize() using { 0 <= chunks_remaining; chunks_remaining < 4; }; }
    have chunks_remaining == 0;
    have chunks_cursor == chunks_tail;
    step_until(function.exit);
    have forall (k: int32) {
        0 <= k and k < bytes.len() as uint32 as int32 implies bytes[k] == old(bytes[k])
    } by { intro(); intro(); solve(); }
    solve();
}
