verifying "nested.rs";
fn array_len() -> usize { ensures result == 8u64; }
fn array_mut() -> u8 { ensures result == 9; }

fn nested(bytes: &[u8]) -> usize {
    requires bytes.len() == 8u64;
    views bytes[0..8];
    ensures result == 0u64;
    ensures forall (k: int32) { 0 <= k and k < 8 implies bytes[k] == old(bytes[k]) };
} by {
    step_until(loop(0));
    have viewable(bytes[0..8]) by {
        transport(at(function.entry, viewable(bytes[0..8])), viewable(bytes[0..8])) using { at(function.entry, viewable(bytes[0..8])); };
    }
    have __rust_mir_8_remaining == 8u64;
    have 8u64 - __rust_mir_8_remaining == 0u64 by { rewrite(__rust_mir_8_remaining == 8u64); solve(); }
    have __rust_mir_8_cursor == bytes + (8u64 - __rust_mir_8_remaining) by { rewrite(8u64 - __rust_mir_8_remaining == 0u64); solve(); }
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
            have 4u64 <= __rust_mir_8_remaining;
            have 8u64 - __rust_mir_8_remaining <= 4u64 by { solve() using { 4u64 <= __rust_mir_8_remaining; __rust_mir_8_remaining <= 8u64; }; }
            mark outer;
            step_until(loop(1));
            have __rust_mir_8_remaining == at(outer, __rust_mir_8_remaining) - 4u64;
            have __rust_mir_8_remaining <= 4u64 by {
                solve() using { __rust_mir_8_remaining == at(outer, __rust_mir_8_remaining) - 4u64; 4u64 <= at(outer, __rust_mir_8_remaining); at(outer, __rust_mir_8_remaining) <= 8u64; };
            }
            have (at(outer, __rust_mir_8_remaining) - 4u64) % 4u64 == at(outer, __rust_mir_8_remaining % 4u64) by {
                normalize() using { 4u64 <= at(outer, __rust_mir_8_remaining); };
            }
            have __rust_mir_8_remaining % 4u64 == 0u64 by {
                rewrite(__rust_mir_8_remaining == at(outer, __rust_mir_8_remaining) - 4u64);
                rewrite((at(outer, __rust_mir_8_remaining) - 4u64) % 4u64 == at(outer, __rust_mir_8_remaining % 4u64)); solve();
            }
            have at(outer, __rust_mir_8_cursor) + 4 == bytes + ((8u64 - at(outer, __rust_mir_8_remaining)) + 4u64) by {
                solve() using {
                    at(outer, __rust_mir_8_cursor) == bytes + (8u64 - at(outer, __rust_mir_8_remaining));
                    8u64 - at(outer, __rust_mir_8_remaining) <= 4u64;
                };
            }
            have 8u64 - __rust_mir_8_remaining == (8u64 - at(outer, __rust_mir_8_remaining)) + 4u64 by {
                solve() using { __rust_mir_8_remaining == at(outer, __rust_mir_8_remaining) - 4u64; 4u64 <= at(outer, __rust_mir_8_remaining); at(outer, __rust_mir_8_remaining) <= 8u64; };
            }
            have __rust_mir_8_cursor == bytes + (8u64 - __rust_mir_8_remaining) by {
                rewrite(8u64 - __rust_mir_8_remaining == (8u64 - at(outer, __rust_mir_8_remaining)) + 4u64); solve();
            }
            have 4u64 <= 8u64 - __rust_mir_8_remaining by { solve() using { __rust_mir_8_remaining <= 4u64; }; }
            have __rust_mir_17_remaining == 4u64;
            have (8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining == 8u64 - at(outer, __rust_mir_8_remaining) by {
                solve() using { __rust_mir_17_remaining == 4u64; __rust_mir_8_remaining == at(outer, __rust_mir_8_remaining) - 4u64; 4u64 <= at(outer, __rust_mir_8_remaining); at(outer, __rust_mir_8_remaining) <= 8u64; };
            }
            have __rust_mir_17_cursor == bytes + ((8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining) by {
                rewrite((8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining == 8u64 - at(outer, __rust_mir_8_remaining)); solve();
            }
            have viewable(bytes[0..8]) by {
                transport(at(outer, viewable(bytes[0..8])), viewable(bytes[0..8])) using { at(outer, viewable(bytes[0..8])); };
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
                    have 2u64 <= __rust_mir_17_remaining;
                    have (8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining <= 6u64 by {
                        solve() using { 2u64 <= __rust_mir_17_remaining; __rust_mir_17_remaining <= 4u64; 4u64 <= 8u64 - __rust_mir_8_remaining; __rust_mir_8_remaining <= 4u64; };
                    }
                    have ((8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining) + 1u64 < 8u64 by {
                        solve() using { (8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining <= 6u64; };
                    }
                    have (8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining < 8u64 by {
                        solve() using { (8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining <= 6u64; };
                    }
                    mark inner;
                    step_until(back_edge());
                    have viewable(bytes[0..8]) by {
                        transport(at(inner, viewable(bytes[0..8])), viewable(bytes[0..8])) using { at(inner, viewable(bytes[0..8])); };
                    }
                    have __rust_mir_17_remaining == at(inner, __rust_mir_17_remaining) - 2u64;
                    have (at(inner, __rust_mir_17_remaining) - 2u64) % 2u64 == at(inner, __rust_mir_17_remaining % 2u64) by {
                        normalize() using { 2u64 <= at(inner, __rust_mir_17_remaining); };
                    }
                    have __rust_mir_17_remaining % 2u64 == 0u64 by {
                        rewrite(__rust_mir_17_remaining == at(inner, __rust_mir_17_remaining) - 2u64);
                        rewrite((at(inner, __rust_mir_17_remaining) - 2u64) % 2u64 == at(inner, __rust_mir_17_remaining % 2u64)); solve();
                    }
                    have __rust_mir_17_remaining <= 4u64 by {
                        solve() using { __rust_mir_17_remaining == at(inner, __rust_mir_17_remaining) - 2u64; 2u64 <= at(inner, __rust_mir_17_remaining); at(inner, __rust_mir_17_remaining) <= 4u64; };
                    }
                    have at(inner, __rust_mir_17_cursor) + 2 == bytes + (((8u64 - __rust_mir_8_remaining) - at(inner, __rust_mir_17_remaining)) + 2u64) by {
                        solve() using {
                            at(inner, __rust_mir_17_cursor) == bytes + ((8u64 - __rust_mir_8_remaining) - at(inner, __rust_mir_17_remaining));
                            (8u64 - __rust_mir_8_remaining) - at(inner, __rust_mir_17_remaining) <= 6u64;
                        };
                    }
                    have (8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining == ((8u64 - __rust_mir_8_remaining) - at(inner, __rust_mir_17_remaining)) + 2u64 by {
                        solve() using {
                            __rust_mir_17_remaining == at(inner, __rust_mir_17_remaining) - 2u64; 2u64 <= at(inner, __rust_mir_17_remaining); at(inner, __rust_mir_17_remaining) <= 4u64;
                            4u64 <= 8u64 - __rust_mir_8_remaining; __rust_mir_8_remaining <= 4u64;
                        };
                    }
                    have __rust_mir_17_cursor == bytes + ((8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining) by {
                        rewrite((8u64 - __rust_mir_8_remaining) - __rust_mir_17_remaining == ((8u64 - __rust_mir_8_remaining) - at(inner, __rust_mir_17_remaining)) + 2u64); solve();
                    }
                    have __rust_mir_17_remaining < at(inner, __rust_mir_17_remaining) by {
                        solve() using { __rust_mir_17_remaining == at(inner, __rust_mir_17_remaining) - 2u64; 2u64 <= at(inner, __rust_mir_17_remaining); };
                    }
                    close_invariants();
                }
            }
            have __rust_mir_17_remaining < 2u64 by {
                cases {
                    not (0u64 < __rust_mir_17_remaining) => {
                        solve() using { not 0u64 < __rust_mir_17_remaining; };
                    }
                    not (2u64 <= __rust_mir_17_remaining) => { assumption(); }
                }
            }
            have __rust_mir_17_remaining % 2u64 == __rust_mir_17_remaining by { normalize() using { __rust_mir_17_remaining < 2u64; }; }
            have __rust_mir_17_remaining == 0u64 by {
                solve() using { __rust_mir_17_remaining % 2u64 == __rust_mir_17_remaining; __rust_mir_17_remaining % 2u64 == 0u64; };
            }
            step_until(back_edge());
            have viewable(bytes[0..8]) by {
                transport(at(outer, viewable(bytes[0..8])), viewable(bytes[0..8])) using { at(outer, viewable(bytes[0..8])); };
            }
            have __rust_mir_8_remaining == at(outer, __rust_mir_8_remaining) - 4u64;
            have __rust_mir_8_remaining < at(outer, __rust_mir_8_remaining) by {
                solve() using { __rust_mir_8_remaining == at(outer, __rust_mir_8_remaining) - 4u64; 4u64 <= at(outer, __rust_mir_8_remaining); };
            }
            have __rust_mir_8_remaining <= 8u64 by { solve() using { __rust_mir_8_remaining <= 4u64; }; }
            close_invariants();
        }
    }
    have __rust_mir_8_remaining < 4u64 by {
        cases {
            not (0u64 < __rust_mir_8_remaining) => {
                solve() using { not 0u64 < __rust_mir_8_remaining; };
            }
            not (4u64 <= __rust_mir_8_remaining) => { assumption(); }
        }
    }
    have __rust_mir_8_remaining % 4u64 == __rust_mir_8_remaining by { normalize() using { __rust_mir_8_remaining < 4u64; }; }
    have __rust_mir_8_remaining == 0u64;
    step_until(function.exit);
    have forall (k: int32) { 0 <= k and k < 8 implies bytes[k] == old(bytes[k]) } by {
        intro(); intro(); solve();
    }
    solve();
}

fn empty_array_len() -> usize { ensures result == 0u64; }
fn medium_array_len() -> usize { ensures result == 1024u64; }
fn large_array_len() -> usize { ensures result == 1000000u64; }
fn array_read(index: usize) -> u8 {
    requires index < 8u64;
    ensures result == 7;
}
