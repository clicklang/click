verifying "nested.rs";
fn array_len() -> usize { ensures result == 8u64; } by { execute(); simp(); }
fn array_mut() -> u8 { ensures result == 9; } by { execute(); simp(); }

fn nested(bytes: &[u8]) -> usize {
    requires bytes.len() == 8u64;
    views bytes[0..8];
    ensures result == 0u64;
    ensures forall (k: int32) { 0 <= k and k < 8 implies bytes[k] == old(bytes[k]) };
} by {
    execute_until(loop(0));
    have viewable(bytes[0..8]) by {
        transport(at(function.entry, viewable(bytes[0..8])), viewable(bytes[0..8])) using { at(function.entry, viewable(bytes[0..8])); }
    }
    have __rust_mir_8_remaining == 8u64 by { simp(); }
    have 8u64 - __rust_mir_8_remaining == 0u64 by { rewrite(__rust_mir_8_remaining == 8u64); simp(); }
    have __rust_mir_8_cursor == bytes + (8u64 - __rust_mir_8_remaining) by { rewrite(8u64 - __rust_mir_8_remaining == 0u64); simp(); }
    loop {
        decreases __rust_mir_8_remaining;
        views bytes[0..8];
        invariant viewable(bytes[0..8]);
        invariant __rust_mir_8_size == 4u64;
        invariant __rust_mir_8_remaining <= 8u64;
        invariant __rust_mir_8_remaining % 4u64 == 0u64;
        invariant __rust_mir_8_cursor == bytes + (8u64 - __rust_mir_8_remaining);
        invariant __rust_mir_14_live == 0;
        invariant __rust_mir_15_live == 0;
        invariant __rust_mir_17_live == 0;
        preserve by {
            have 4u64 <= __rust_mir_8_remaining by { simp(); }
            have 8u64 - __rust_mir_8_remaining <= 4u64 by { arithmetic() using { 4u64 <= __rust_mir_8_remaining; __rust_mir_8_remaining <= 8u64; } }
            mark outer;
            execute_until(loop(1));
            have __rust_mir_8_remaining == at(outer, __rust_mir_8_remaining) - 4u64 by { simp(); }
            have __rust_mir_8_remaining <= 4u64 by {
                arithmetic() using { __rust_mir_8_remaining == at(outer, __rust_mir_8_remaining) - 4u64; 4u64 <= at(outer, __rust_mir_8_remaining); at(outer, __rust_mir_8_remaining) <= 8u64; }
            }
            have (at(outer, __rust_mir_8_remaining) - 4u64) % 4u64 == at(outer, __rust_mir_8_remaining % 4u64) by {
                normalize() using { 4u64 <= at(outer, __rust_mir_8_remaining); }
            }
            have __rust_mir_8_remaining % 4u64 == 0u64 by {
                rewrite(__rust_mir_8_remaining == at(outer, __rust_mir_8_remaining) - 4u64);
                rewrite((at(outer, __rust_mir_8_remaining) - 4u64) % 4u64 == at(outer, __rust_mir_8_remaining % 4u64)); simp();
            }
            have at(outer, __rust_mir_8_cursor) + 4 == bytes + ((8u64 - at(outer, __rust_mir_8_remaining)) + 4u64) by {
                arithmetic() using {
                    at(outer, __rust_mir_8_cursor) == bytes + (8u64 - at(outer, __rust_mir_8_remaining));
                    8u64 - at(outer, __rust_mir_8_remaining) <= 4u64;
                }
            }
            have 8u64 - __rust_mir_8_remaining == (8u64 - at(outer, __rust_mir_8_remaining)) + 4u64 by {
                arithmetic() using { __rust_mir_8_remaining == at(outer, __rust_mir_8_remaining) - 4u64; 4u64 <= at(outer, __rust_mir_8_remaining); at(outer, __rust_mir_8_remaining) <= 8u64; }
            }
            have __rust_mir_8_cursor == bytes + (8u64 - __rust_mir_8_remaining) by {
                rewrite(8u64 - __rust_mir_8_remaining == (8u64 - at(outer, __rust_mir_8_remaining)) + 4u64); simp();
            }
            have 4u64 <= 8u64 - __rust_mir_8_remaining by { arithmetic() using { __rust_mir_8_remaining <= 4u64; } }
            have __rust_mir_17_remaining == 4u64 by { simp(); }
            have (8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining == 8u64 - at(outer, __rust_mir_8_remaining) by {
                arithmetic() using { __rust_mir_17_remaining == 4u64; __rust_mir_8_remaining == at(outer, __rust_mir_8_remaining) - 4u64; 4u64 <= at(outer, __rust_mir_8_remaining); at(outer, __rust_mir_8_remaining) <= 8u64; }
            }
            have __rust_mir_17_cursor == bytes + ((8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining) by {
                rewrite((8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining == 8u64 - at(outer, __rust_mir_8_remaining)); simp();
            }
            have viewable(bytes[0..8]) by {
                transport(at(outer, viewable(bytes[0..8])), viewable(bytes[0..8])) using { at(outer, viewable(bytes[0..8])); }
            }
            loop {
                decreases __rust_mir_17_remaining;
                views bytes[0..8];
                invariant viewable(bytes[0..8]);
                invariant __rust_mir_8_remaining <= 4u64;
                invariant __rust_mir_8_remaining % 4u64 == 0u64;
                invariant __rust_mir_8_cursor == bytes + (8u64 - __rust_mir_8_remaining);
                invariant __rust_mir_17_size == 2u64;
                invariant __rust_mir_17_remaining <= 4u64;
                invariant __rust_mir_17_remaining % 2u64 == 0u64;
                invariant __rust_mir_17_cursor == bytes + ((8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining);
                invariant 4u64 <= 8u64 - __rust_mir_8_remaining;
                preserve by {
                    have 2u64 <= __rust_mir_17_remaining by { simp(); }
                    have (8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining <= 6u64 by {
                        arithmetic() using { 2u64 <= __rust_mir_17_remaining; __rust_mir_17_remaining <= 4u64; 4u64 <= 8u64 - __rust_mir_8_remaining; __rust_mir_8_remaining <= 4u64; }
                    }
                    have ((8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining) + 1u64 < 8u64 by {
                        arithmetic() using { (8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining <= 6u64; }
                    }
                    have (8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining < 8u64 by {
                        arithmetic() using { (8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining <= 6u64; }
                    }
                    mark inner;
                    execute_until(back_edge());
                    have viewable(bytes[0..8]) by {
                        transport(at(inner, viewable(bytes[0..8])), viewable(bytes[0..8])) using { at(inner, viewable(bytes[0..8])); }
                    }
                    have __rust_mir_17_remaining == at(inner, __rust_mir_17_remaining) - 2u64 by { simp(); }
                    have (at(inner, __rust_mir_17_remaining) - 2u64) % 2u64 == at(inner, __rust_mir_17_remaining % 2u64) by {
                        normalize() using { 2u64 <= at(inner, __rust_mir_17_remaining); }
                    }
                    have __rust_mir_17_remaining % 2u64 == 0u64 by {
                        rewrite(__rust_mir_17_remaining == at(inner, __rust_mir_17_remaining) - 2u64);
                        rewrite((at(inner, __rust_mir_17_remaining) - 2u64) % 2u64 == at(inner, __rust_mir_17_remaining % 2u64)); simp();
                    }
                    have __rust_mir_17_remaining <= 4u64 by {
                        arithmetic() using { __rust_mir_17_remaining == at(inner, __rust_mir_17_remaining) - 2u64; 2u64 <= at(inner, __rust_mir_17_remaining); at(inner, __rust_mir_17_remaining) <= 4u64; }
                    }
                    have at(inner, __rust_mir_17_cursor) + 2 == bytes + (((8u64 - __rust_mir_8_remaining) - at(inner, __rust_mir_17_remaining)) + 2u64) by {
                        arithmetic() using {
                            at(inner, __rust_mir_17_cursor) == bytes + ((8u64 - __rust_mir_8_remaining) - at(inner, __rust_mir_17_remaining));
                            (8u64 - __rust_mir_8_remaining) - at(inner, __rust_mir_17_remaining) <= 6u64;
                        }
                    }
                    have (8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining == ((8u64 - __rust_mir_8_remaining) - at(inner, __rust_mir_17_remaining)) + 2u64 by {
                        arithmetic() using {
                            __rust_mir_17_remaining == at(inner, __rust_mir_17_remaining) - 2u64; 2u64 <= at(inner, __rust_mir_17_remaining); at(inner, __rust_mir_17_remaining) <= 4u64;
                            4u64 <= 8u64 - __rust_mir_8_remaining; __rust_mir_8_remaining <= 4u64;
                        }
                    }
                    have __rust_mir_17_cursor == bytes + ((8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining) by {
                        rewrite((8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining == ((8u64 - __rust_mir_8_remaining) - at(inner, __rust_mir_17_remaining)) + 2u64); simp();
                    }
                    have __rust_mir_17_remaining < at(inner, __rust_mir_17_remaining) by {
                        arithmetic() using { __rust_mir_17_remaining == at(inner, __rust_mir_17_remaining) - 2u64; 2u64 <= at(inner, __rust_mir_17_remaining); }
                    }
                    close_invariants();
                }
            }
            have __rust_mir_17_remaining < 2u64 by {
                cases {
                    not (0u64 < __rust_mir_17_remaining) => {
                        arithmetic() using { not 0u64 < __rust_mir_17_remaining; }
                    }
                    not (2u64 <= __rust_mir_17_remaining) => { assumption(); }
                }
            }
            have __rust_mir_17_remaining % 2u64 == __rust_mir_17_remaining by { normalize() using { __rust_mir_17_remaining < 2u64; } }
            have __rust_mir_17_remaining == 0u64 by {
                arithmetic() using { __rust_mir_17_remaining % 2u64 == __rust_mir_17_remaining; __rust_mir_17_remaining % 2u64 == 0u64; }
            }
            execute_until(back_edge());
            have viewable(bytes[0..8]) by {
                transport(at(outer, viewable(bytes[0..8])), viewable(bytes[0..8])) using { at(outer, viewable(bytes[0..8])); }
            }
            have __rust_mir_8_remaining == at(outer, __rust_mir_8_remaining) - 4u64 by { simp(); }
            have __rust_mir_8_remaining < at(outer, __rust_mir_8_remaining) by {
                arithmetic() using { __rust_mir_8_remaining == at(outer, __rust_mir_8_remaining) - 4u64; 4u64 <= at(outer, __rust_mir_8_remaining); }
            }
            have __rust_mir_8_remaining <= 8u64 by { arithmetic() using { __rust_mir_8_remaining <= 4u64; } }
            close_invariants();
        }
    }
    have __rust_mir_8_remaining < 4u64 by {
        cases {
            not (0u64 < __rust_mir_8_remaining) => {
                arithmetic() using { not 0u64 < __rust_mir_8_remaining; }
            }
            not (4u64 <= __rust_mir_8_remaining) => { assumption(); }
        }
    }
    have __rust_mir_8_remaining % 4u64 == __rust_mir_8_remaining by { normalize() using { __rust_mir_8_remaining < 4u64; } }
    have __rust_mir_8_remaining == 0u64 by { simp(); }
    execute();
    have forall (k: int32) { 0 <= k and k < 8 implies bytes[k] == old(bytes[k]) } by {
        intro(); intro(); simp();
    }
    simp();
}

fn empty_array_len() -> usize { ensures result == 0u64; } by { execute(); simp(); }
fn medium_array_len() -> usize { ensures result == 1024u64; } by { execute(); simp(); }
fn large_array_len() -> usize { ensures result == 1000000u64; } by { execute(); simp(); }
fn array_read(index: usize) -> u8 {
    requires index < 8u64;
    ensures result == 7;
} by { execute(); simp(); }
