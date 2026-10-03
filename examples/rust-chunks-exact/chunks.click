verifying "chunks.rs";

uint64 cover(const uint8* bytes, uint64 bytes_len) {
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
    execute_until(statement(22));
    have viewable(bytes[0..(int32)(uint32)bytes_len]) by {
        transport(at(function.entry, viewable(bytes[0..(int32)(uint32)bytes_len])), viewable(bytes[0..(int32)(uint32)bytes_len])) using {
            at(function.entry, viewable(bytes[0..(int32)(uint32)bytes_len]));
            0 <= (int32)(uint32)bytes_len;
        }
    }
    have bytes_len <= 2147483647u64 by { normalize() using { bytes_len <= 1000u64; } }
    have (((int32)(uint32)(bytes_len - bytes_len % 4u64)) % 4) == 0 by { normalize() using { bytes_len <= 2147483647u64; } }
    have chunks_remaining == (int32)(uint32)(bytes_len - bytes_len % 4u64) by { simp(); }
    have chunks_remaining % 4 == 0 by {
        rewrite(chunks_remaining == (int32)(uint32)(bytes_len - bytes_len % 4u64)); simp();
    }
    loop {
        decreases chunks_remaining;
        views bytes[0..(int32)(uint32)bytes_len];
        invariant viewable(bytes[0..(int32)(uint32)bytes_len]);
        invariant bytes_len <= 1000u64;
        invariant 0 <= (int32)(uint32)bytes_len and ((int32)(uint32)bytes_len) <= 1000;
        invariant 0 <= (int32)(uint32)(bytes_len - bytes_len % 4u64) and ((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= (int32)(uint32)bytes_len;
        invariant ((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 1000;
        invariant chunks_size == 4u64;
        invariant chunks_tail_len == bytes_len % 4u64;
        invariant tail_len == chunks_tail_len;
        invariant chunks_tail == bytes + (int32)(uint32)(bytes_len - bytes_len % 4u64);
        invariant tail == chunks_tail;
        invariant 0 <= chunks_remaining and chunks_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64);
        invariant chunks_remaining % 4 == 0;
        invariant chunks_cursor == bytes + ((int32)(uint32)(bytes_len - bytes_len % 4u64) - chunks_remaining);
        invariant 0 <= ((int32)(uint32)(bytes_len - bytes_len % 4u64) - chunks_remaining) and ((int32)(uint32)(bytes_len - bytes_len % 4u64) - chunks_remaining) <= 1000;
        preserve by {
            have 4 <= chunks_remaining by { simp(); }
            mark iteration;
            have ((int32)(uint32)(bytes_len - bytes_len % 4u64) - chunks_remaining) + 4 <= (int32)(uint32)bytes_len by {
                arithmetic() using {
                    4 <= chunks_remaining;
                    chunks_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64);
                    ((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= (int32)(uint32)bytes_len;
                    0 <= (int32)(uint32)bytes_len; ((int32)(uint32)bytes_len) <= 1000;
                    0 <= (int32)(uint32)(bytes_len - bytes_len % 4u64);
                }
            }
            execute_until(statement(42)); step();
            have viewable(bytes[0..(int32)(uint32)bytes_len]) by {
                transport(at(iteration, viewable(bytes[0..(int32)(uint32)bytes_len])), viewable(bytes[0..(int32)(uint32)bytes_len])) using {
                    at(iteration, viewable(bytes[0..(int32)(uint32)bytes_len]));
                    0 <= (int32)(uint32)bytes_len;
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
            have chunks_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64) by {
                arithmetic() using {
                    chunks_remaining == at(iteration, chunks_remaining) - 4;
                    at(iteration, 4 <= chunks_remaining);
                    at(iteration, chunks_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64));
                    0 <= (int32)(uint32)(bytes_len - bytes_len % 4u64);
                    ((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 1000;
                }
            }
            have chunks_cursor == at(iteration, chunks_cursor) + 4 by { simp(); }
            have ((int32)(uint32)(bytes_len - bytes_len % 4u64) - chunks_remaining) == at(iteration, (int32)(uint32)(bytes_len - bytes_len % 4u64) - chunks_remaining) + 4 by {
                arithmetic() using {
                    chunks_remaining == at(iteration, chunks_remaining) - 4;
                    at(iteration, 4 <= chunks_remaining);
                    at(iteration, chunks_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64));
                    0 <= (int32)(uint32)(bytes_len - bytes_len % 4u64);
                    ((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 1000;
                }
            }
            have at(iteration, chunks_cursor) + 4 == bytes + (at(iteration, (int32)(uint32)(bytes_len - bytes_len % 4u64) - chunks_remaining) + 4) by {
                arithmetic() using {
                    at(iteration, chunks_cursor == bytes + ((int32)(uint32)(bytes_len - bytes_len % 4u64) - chunks_remaining));
                    at(iteration, 0 <= ((int32)(uint32)(bytes_len - bytes_len % 4u64) - chunks_remaining));
                    at(iteration, ((int32)(uint32)(bytes_len - bytes_len % 4u64) - chunks_remaining) <= 1000);
                }
            }
            have chunks_cursor == bytes + ((int32)(uint32)(bytes_len - bytes_len % 4u64) - chunks_remaining) by {
                rewrite(((int32)(uint32)(bytes_len - bytes_len % 4u64) - chunks_remaining) == at(iteration, (int32)(uint32)(bytes_len - bytes_len % 4u64) - chunks_remaining) + 4); simp();
            }
            close_invariants by {
                extract(((int32)((uint32)bytes_len)) <= 1000);
                extract(at(statement(23).entry, 0) <= at(statement(23).entry, chunks_remaining));
                extract(at(statement(23).entry, chunks_remaining) <= at(statement(23).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))));
                extract(at(statement(23).entry, 0) <= at(statement(23).entry, (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - chunks_remaining)));
                extract(at(statement(23).entry, (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - chunks_remaining)) <= at(statement(23).entry, 1000));
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
                                    premise 0: chunks_remaining <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) => chunks_remaining <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64))));
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
                                                premise 0: 0 <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) => 0 <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64))));
                                                premise 1: ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000 => ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000;
                                                premise 2: at(statement(23).entry, chunks_remaining) <= at(statement(23).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) => at(statement(23).entry, chunks_remaining) <= at(statement(23).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))));
                                                premise 3: at(statement(23).entry, ((int32)((uint32)chunks_size))) <= at(statement(23).entry, chunks_remaining) => at(statement(23).entry, ((int32)((uint32)chunks_size))) <= at(statement(23).entry, chunks_remaining);
                                                interval_from_affine 0 (((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) (0) (2147483647);
                                                interval_from_affine 1 (((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) (-2147483648) (1000);
                                                interval_intersect 4, 5 (0) (1000);
                                                add 2, 1 => (at(statement(23).entry, chunks_remaining) + ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) <= (at(statement(23).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) + 1000);
                                                interval_from_affine 3 (at(statement(23).entry, chunks_remaining)) (4) (2147483647);
                                                interval_from_affine 7 (at(statement(23).entry, chunks_remaining)) (-2147483648) (1000);
                                                interval_intersect 8, 9 (4) (1000);
                                                interval_atom (4) (4) (4);
                                                interval_subtract 10, 11 10 (0) (996);
                                                interval_subtract 6, 12 6 (-996) (1000);
                                                trivial => -4 <= 0;
                                                add 2, 14 => (at(statement(23).entry, chunks_remaining) + -4) <= (at(statement(23).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) + 0);
                                                affine_conclusion 15 13 => 0 <= (at(loop(0).entry, chunks_remaining) - chunks_remaining);
                                                conclusion 16;
                                            }
                                        } and {
                                            arithmetic_certificate signed_int32 {
                                                premise 0: 0 <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) => 0 <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64))));
                                                premise 1: ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000 => ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000;
                                                premise 2: at(statement(23).entry, chunks_remaining) <= at(statement(23).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) => at(statement(23).entry, chunks_remaining) <= at(statement(23).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))));
                                                premise 3: at(statement(23).entry, ((int32)((uint32)chunks_size))) <= at(statement(23).entry, chunks_remaining) => at(statement(23).entry, ((int32)((uint32)chunks_size))) <= at(statement(23).entry, chunks_remaining);
                                                interval_from_affine 0 (((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) (0) (2147483647);
                                                interval_from_affine 1 (((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) (-2147483648) (1000);
                                                interval_intersect 4, 5 (0) (1000);
                                                add 2, 1 => (at(statement(23).entry, chunks_remaining) + ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) <= (at(statement(23).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) + 1000);
                                                interval_from_affine 3 (at(statement(23).entry, chunks_remaining)) (4) (2147483647);
                                                interval_from_affine 7 (at(statement(23).entry, chunks_remaining)) (-2147483648) (1000);
                                                interval_intersect 8, 9 (4) (1000);
                                                interval_atom (4) (4) (4);
                                                interval_subtract 10, 11 10 (0) (996);
                                                interval_subtract 6, 12 6 (-996) (1000);
                                                add 1, 3 => (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) + at(statement(23).entry, ((int32)((uint32)chunks_size)))) <= (1000 + at(statement(23).entry, chunks_remaining));
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
                                                premise 0: ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000 => ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000;
                                                premise 1: at(statement(23).entry, chunks_remaining) <= at(statement(23).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) => at(statement(23).entry, chunks_remaining) <= at(statement(23).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))));
                                                premise 2: at(statement(23).entry, ((int32)((uint32)chunks_size))) <= at(statement(23).entry, chunks_remaining) => at(statement(23).entry, ((int32)((uint32)chunks_size))) <= at(statement(23).entry, chunks_remaining);
                                                add 1, 0 => (at(statement(23).entry, chunks_remaining) + ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) <= (at(statement(23).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) + 1000);
                                                interval_from_affine 2 (at(statement(23).entry, chunks_remaining)) (4) (2147483647);
                                                interval_from_affine 3 (at(statement(23).entry, chunks_remaining)) (-2147483648) (1000);
                                                interval_intersect 4, 5 (4) (1000);
                                                interval_atom (4) (4) (4);
                                                interval_subtract 6, 7 6 (0) (996);
                                                trivial => -3 <= 0;
                                                affine_conclusion 9 8 => chunks_remaining < at(statement(23).entry, chunks_remaining);
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
        0 <= k and k < (int32)(uint32)bytes_len implies bytes[k] == old(bytes[k])
    } by { intro(); intro(); simp(); }
    simp();
}
