verifying "chunks.rs";

fn cover(bytes: &[u8]) -> usize {
    requires bytes.len() <= 1000u64;
    views bytes[0..((bytes.len() as uint32) as int32)];
    ensures result == bytes.len() % 4u64;
    ensures forall (k: int32) {
        0 <= k and k < ((bytes.len() as uint32) as int32) implies bytes[k] == old(bytes[k])
    };
} by {
    have bytes.len() % 4u64 <= bytes.len() by { normalize(); }
    have bytes.len() - bytes.len() % 4u64 <= bytes.len() by { normalize() using { bytes.len() % 4u64 <= bytes.len(); } }
    have bytes.len() - bytes.len() % 4u64 <= 1000u64 by { normalize() using { bytes.len() - bytes.len() % 4u64 <= bytes.len(); bytes.len() <= 1000u64; } }
    have bytes.len() - bytes.len() % 4u64 <= 2147483647u64 by { normalize() using { bytes.len() - bytes.len() % 4u64 <= 1000u64; } }
    have 0 <= (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) by { normalize() using { bytes.len() - bytes.len() % 4u64 <= 2147483647u64; } }
    have ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 1000 by { solve(); }
    have bytes.len() <= 2147483647u64 by { normalize() using { bytes.len() <= 1000u64; } }
    have ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= ((bytes.len() as uint32) as int32) by { normalize() using { bytes.len() - bytes.len() % 4u64 <= bytes.len(); bytes.len() <= 2147483647u64; } }
    step_until(region(22));
    have viewable(bytes[0..((bytes.len() as uint32) as int32)]) by {
        transport(at(function.entry, viewable(bytes[0..((bytes.len() as uint32) as int32)])), viewable(bytes[0..((bytes.len() as uint32) as int32)])) using {
            at(function.entry, viewable(bytes[0..((bytes.len() as uint32) as int32)]));
            0 <= ((bytes.len() as uint32) as int32);
        }
    }
    have bytes.len() <= 2147483647u64 by { normalize() using { bytes.len() <= 1000u64; } }
    have (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) % 4) == 0 by { normalize() using { bytes.len() <= 2147483647u64; } }
    have chunks_remaining == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) by { solve(); }
    have chunks_remaining % 4 == 0 by {
        rewrite(chunks_remaining == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); solve();
    }
    loop {
        decreases chunks_remaining;
        views bytes[0..((bytes.len() as uint32) as int32)];
        invariant viewable(bytes[0..((bytes.len() as uint32) as int32)]);
        invariant bytes.len() <= 1000u64;
        invariant 0 <= ((bytes.len() as uint32) as int32) and (((bytes.len() as uint32) as int32)) <= 1000;
        invariant 0 <= (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) and ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= ((bytes.len() as uint32) as int32);
        invariant ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 1000;
        invariant chunks_size == 4u64;
        invariant chunks_tail_len == bytes.len() % 4u64;
        invariant tail_len == chunks_tail_len;
        invariant chunks_tail == bytes + (((bytes.len() - bytes.len() % 4u64) as uint32) as int32);
        invariant tail == chunks_tail;
        invariant 0 <= chunks_remaining and chunks_remaining <= (((bytes.len() - bytes.len() % 4u64) as uint32) as int32);
        invariant chunks_remaining % 4 == 0;
        invariant chunks_cursor == bytes + ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - chunks_remaining);
        invariant 0 <= ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - chunks_remaining) and ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - chunks_remaining) <= 1000;
        preserve by {
            have 4 <= chunks_remaining by { solve(); }
            mark iteration;
            have ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - chunks_remaining) + 4 <= ((bytes.len() as uint32) as int32) by {
                solve() using {
                    4 <= chunks_remaining;
                    chunks_remaining <= (((bytes.len() - bytes.len() % 4u64) as uint32) as int32);
                    ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= ((bytes.len() as uint32) as int32);
                    0 <= ((bytes.len() as uint32) as int32); (((bytes.len() as uint32) as int32)) <= 1000;
                    0 <= (((bytes.len() - bytes.len() % 4u64) as uint32) as int32);
                }
            }
            step_until(region(42)); step();
            have viewable(bytes[0..((bytes.len() as uint32) as int32)]) by {
                transport(at(iteration, viewable(bytes[0..((bytes.len() as uint32) as int32)])), viewable(bytes[0..((bytes.len() as uint32) as int32)])) using {
                    at(iteration, viewable(bytes[0..((bytes.len() as uint32) as int32)]));
                    0 <= ((bytes.len() as uint32) as int32);
                }
            }
            have chunks_remaining == at(iteration, chunks_remaining) - 4 by { solve(); }
            have (at(iteration, chunks_remaining) - 4) % 4 == at(iteration, chunks_remaining % 4) by {
                normalize() using { at(iteration, 4 <= chunks_remaining); }
            }
            have chunks_remaining % 4 == 0 by {
                rewrite(chunks_remaining == at(iteration, chunks_remaining) - 4);
                rewrite((at(iteration, chunks_remaining) - 4) % 4 == at(iteration, chunks_remaining % 4)); solve();
            }
            have 0 <= chunks_remaining by {
                solve() using { chunks_remaining == at(iteration, chunks_remaining) - 4; at(iteration, 4 <= chunks_remaining); }
            }
            have chunks_remaining <= (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) by {
                solve() using {
                    chunks_remaining == at(iteration, chunks_remaining) - 4;
                    at(iteration, 4 <= chunks_remaining);
                    at(iteration, chunks_remaining <= (((bytes.len() - bytes.len() % 4u64) as uint32) as int32));
                    0 <= (((bytes.len() - bytes.len() % 4u64) as uint32) as int32);
                    ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 1000;
                }
            }
            have chunks_cursor == at(iteration, chunks_cursor) + 4 by { solve(); }
            have ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - chunks_remaining) == at(iteration, (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - chunks_remaining) + 4 by {
                solve() using {
                    chunks_remaining == at(iteration, chunks_remaining) - 4;
                    at(iteration, 4 <= chunks_remaining);
                    at(iteration, chunks_remaining <= (((bytes.len() - bytes.len() % 4u64) as uint32) as int32));
                    0 <= (((bytes.len() - bytes.len() % 4u64) as uint32) as int32);
                    ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 1000;
                }
            }
            have at(iteration, chunks_cursor) + 4 == bytes + (at(iteration, (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - chunks_remaining) + 4) by {
                solve() using {
                    at(iteration, chunks_cursor == bytes + ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - chunks_remaining));
                    at(iteration, 0 <= ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - chunks_remaining));
                    at(iteration, ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - chunks_remaining) <= 1000);
                }
            }
            have chunks_cursor == bytes + ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - chunks_remaining) by {
                rewrite(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - chunks_remaining) == at(iteration, (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - chunks_remaining) + 4); solve();
            }
            close_invariants() by {
                extract(((((bytes.len() as uint32)) as int32)) <= 1000);
                extract(at(region(23).entry, 0) <= at(region(23).entry, chunks_remaining));
                extract(at(region(23).entry, chunks_remaining) <= at(region(23).entry, (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32))));
                extract(at(region(23).entry, 0) <= at(region(23).entry, ((((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32)) - chunks_remaining)));
                extract(at(region(23).entry, ((((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32)) - chunks_remaining)) <= at(region(23).entry, 1000));
                both {
                    normalize();
                } and {
                    both {
                        intro();
                        normalize();
                    } and {
                        both {
                            intro();
                            intro();
                            both {
                                arithmetic_certificate signed_int32 {
                                    premise 0: 0 <= chunks_remaining => 0 <= chunks_remaining;
                                    conclusion 0;
                                }
                            } and {
                                arithmetic_certificate signed_int32 {
                                    premise 0: chunks_remaining <= (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32)) => chunks_remaining <= (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32));
                                    conclusion 0;
                                }
                            }
                        } and {
                            both {
                                intro();
                                intro();
                                intro();
                                arithmetic_certificate signed_int32 {
                                    premise 0: (chunks_remaining % 4) == 0 => (chunks_remaining % 4) == 0;
                                    conclusion 0;
                                }
                            } and {
                                both {
                                    intro();
                                    intro();
                                    intro();
                                    intro();
                                    intro();
                                    assumption();
                                } and {
                                    both {
                                        intro();
                                        intro();
                                        intro();
                                        intro();
                                        intro();
                                        intro();
                                        both {
                                            arithmetic_certificate signed_int32 {
                                                premise 0: 0 <= (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32)) => 0 <= (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32));
                                                premise 1: (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32)) <= 1000 => (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32)) <= 1000;
                                                premise 2: at(region(23).entry, chunks_remaining) <= at(region(23).entry, (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32))) => at(region(23).entry, chunks_remaining) <= at(region(23).entry, (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32)));
                                                premise 3: at(region(23).entry, ((((chunks_size as uint32)) as int32))) <= at(region(23).entry, chunks_remaining) => at(region(23).entry, ((((chunks_size as uint32)) as int32))) <= at(region(23).entry, chunks_remaining);
                                                interval_from_affine 0 ((((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32))) (0) (2147483647);
                                                interval_from_affine 1 ((((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32))) (-2147483648) (1000);
                                                interval_intersect 4, 5 (0) (1000);
                                                add 2, 1 => (at(region(23).entry, chunks_remaining) + (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32))) <= (at(region(23).entry, (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32))) + 1000);
                                                interval_from_affine 3 (at(region(23).entry, chunks_remaining)) (4) (2147483647);
                                                interval_from_affine 7 (at(region(23).entry, chunks_remaining)) (-2147483648) (1000);
                                                interval_intersect 8, 9 (4) (1000);
                                                interval_atom (4) (4) (4);
                                                interval_subtract 10, 11 10 (0) (996);
                                                interval_subtract 6, 12 6 (-996) (1000);
                                                trivial => -4 <= 0;
                                                add 2, 14 => (at(region(23).entry, chunks_remaining) + -4) <= (at(region(23).entry, (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32))) + 0);
                                                affine_conclusion 15 13 => 0 <= (at(loop(0).entry, chunks_remaining) - chunks_remaining);
                                                conclusion 16;
                                            }
                                        } and {
                                            arithmetic_certificate signed_int32 {
                                                premise 0: 0 <= (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32)) => 0 <= (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32));
                                                premise 1: (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32)) <= 1000 => (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32)) <= 1000;
                                                premise 2: at(region(23).entry, chunks_remaining) <= at(region(23).entry, (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32))) => at(region(23).entry, chunks_remaining) <= at(region(23).entry, (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32)));
                                                premise 3: at(region(23).entry, ((((chunks_size as uint32)) as int32))) <= at(region(23).entry, chunks_remaining) => at(region(23).entry, ((((chunks_size as uint32)) as int32))) <= at(region(23).entry, chunks_remaining);
                                                interval_from_affine 0 ((((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32))) (0) (2147483647);
                                                interval_from_affine 1 ((((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32))) (-2147483648) (1000);
                                                interval_intersect 4, 5 (0) (1000);
                                                add 2, 1 => (at(region(23).entry, chunks_remaining) + (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32))) <= (at(region(23).entry, (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32))) + 1000);
                                                interval_from_affine 3 (at(region(23).entry, chunks_remaining)) (4) (2147483647);
                                                interval_from_affine 7 (at(region(23).entry, chunks_remaining)) (-2147483648) (1000);
                                                interval_intersect 8, 9 (4) (1000);
                                                interval_atom (4) (4) (4);
                                                interval_subtract 10, 11 10 (0) (996);
                                                interval_subtract 6, 12 6 (-996) (1000);
                                                add 1, 3 => ((((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32)) + at(region(23).entry, ((((chunks_size as uint32)) as int32)))) <= (1000 + at(region(23).entry, chunks_remaining));
                                                affine_conclusion 14 13 => (at(loop(0).entry, chunks_remaining) - chunks_remaining) <= 1000;
                                                conclusion 15;
                                            }
                                        }
                                    } and {
                                        both {
                                            arithmetic_certificate signed_int32 {
                                                premise 0: 0 <= chunks_remaining => 0 <= chunks_remaining;
                                                conclusion 0;
                                            }
                                        } and {
                                            arithmetic_certificate signed_int32 {
                                                premise 0: (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32)) <= 1000 => (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32)) <= 1000;
                                                premise 1: at(region(23).entry, chunks_remaining) <= at(region(23).entry, (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32))) => at(region(23).entry, chunks_remaining) <= at(region(23).entry, (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32)));
                                                premise 2: at(region(23).entry, ((((chunks_size as uint32)) as int32))) <= at(region(23).entry, chunks_remaining) => at(region(23).entry, ((((chunks_size as uint32)) as int32))) <= at(region(23).entry, chunks_remaining);
                                                add 1, 0 => (at(region(23).entry, chunks_remaining) + (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32))) <= (at(region(23).entry, (((((bytes.len() - (bytes.len() % 4u64)) as uint32)) as int32))) + 1000);
                                                interval_from_affine 2 (at(region(23).entry, chunks_remaining)) (4) (2147483647);
                                                interval_from_affine 3 (at(region(23).entry, chunks_remaining)) (-2147483648) (1000);
                                                interval_intersect 4, 5 (4) (1000);
                                                interval_atom (4) (4) (4);
                                                interval_subtract 6, 7 6 (0) (996);
                                                trivial => -3 <= 0;
                                                affine_conclusion 9 8 => chunks_remaining < at(region(23).entry, chunks_remaining);
                                                conclusion 10;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    have chunks_remaining < 4 by {
        cases {
            not (0 < chunks_remaining) => {
                have chunks_remaining <= 0 by { solve(); }
                solve() using { chunks_remaining <= 0; }
            }
            not (4 <= chunks_remaining) => { solve(); }
        }
    }
    have chunks_remaining % 4 == chunks_remaining by { normalize() using { 0 <= chunks_remaining; chunks_remaining < 4; } }
    have chunks_remaining == 0 by { solve(); }
    have chunks_cursor == chunks_tail by { solve(); }
    step_until(function.exit);
    have forall (k: int32) {
        0 <= k and k < ((bytes.len() as uint32) as int32) implies bytes[k] == old(bytes[k])
    } by { intro(); intro(); solve(); }
    solve();
}

import click::integer;
