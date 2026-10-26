verifying "sum.rs";
function prefix(bytes: const uint8*, end: int32) -> Integer {
    (0..end).fold(0, |acc, k| {
        acc + to_integer((bytes[k] as int32))
    })
}
fn sum(bytes: &[u8]) -> i32 {
    requires bytes.len() <= 1000u64;
    views bytes[0..((bytes.len() as uint32) as int32)];
    ensures to_integer(result) == old(prefix(bytes, ((bytes.len() as uint32) as int32)));
} by {
    step_until(region(9));
    have 0 <= ((bytes.len() as uint32) as int32) by { solve(); }
    have viewable(bytes[0..((bytes.len() as uint32) as int32)]) by {
        transport(at(function.entry, viewable(bytes[0..((bytes.len() as uint32) as int32)])), viewable(bytes[0..((bytes.len() as uint32) as int32)])) using {
            at(function.entry, viewable(bytes[0..((bytes.len() as uint32) as int32)]));
            0 <= ((bytes.len() as uint32) as int32);
        }
    }
    have prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining)) == 0 by {
        peel(prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining))) using {
            0 >= (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining);
        } solve();
    }
    have to_integer(total) == 0 by {
        solve();
    }
    have to_integer(total) == prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining)) by {
        solve() using {
            to_integer(total) == 0;
            prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining)) == 0;
        }
    }
    // This sidecar chooses an input-prefix invariant; the iterator supplies
    // its remaining slice and cursor, without a processed-count variable.
    loop {
        decreases __rust_iter_3_5_remaining;
        views bytes[0..((bytes.len() as uint32) as int32)];
        invariant viewable(bytes[0..((bytes.len() as uint32) as int32)]);
        invariant bytes.len() <= 1000u64;
        invariant 0 <= __rust_iter_3_5_remaining and __rust_iter_3_5_remaining <= ((bytes.len() as uint32) as int32);
        invariant 0 <= ((bytes.len() as uint32) as int32) and 1000 >= ((bytes.len() as uint32) as int32);
        invariant __rust_iter_3_5_cursor == bytes + (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining);
        invariant 0 <= (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) and 1000 >= (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining);
        invariant 0 <= to_integer(total) and to_integer(total) <= 255 * to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining));
        invariant to_integer(total) == prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining));
        preserve by {
            have 0 < __rust_iter_3_5_remaining by { solve() using { 0 <= __rust_iter_3_5_remaining; not (__rust_iter_3_5_remaining == 0); } }
            have 0 <= __rust_iter_3_5_remaining - 1 by { solve() using { 0 < __rust_iter_3_5_remaining; } }
            have 0 <= to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining)) by {
                apply(integer::int32_less_equal_to_integer(0, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining))) using {
                    0 <= (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining);
                }
            }
            have to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining)) <= 1000 by {
                apply(integer::int32_less_equal_to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining), 1000)) using {
                    1000 >= (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining);
                }
            }
            have to_integer(total) <= 255000 by {
                solve() using {
                    to_integer(total) <= 255 * to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining));
                    to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining)) <= 1000;
                }
            }
            have __rust_iter_3_5_remaining - 1 <= ((bytes.len() as uint32) as int32) by {
                apply(integer::int32_nonnegative_predecessor_upper_bound(__rust_iter_3_5_remaining, ((bytes.len() as uint32) as int32))) using {
                    0 <= __rust_iter_3_5_remaining;
                    __rust_iter_3_5_remaining <= ((bytes.len() as uint32) as int32);
                }
            }
            step_until(region(15));
            have 0 <= __rust_iter_3_5_remaining by { solve(); }
            have __rust_iter_3_5_remaining <= ((bytes.len() as uint32) as int32) by { solve(); }
            have (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) < ((bytes.len() as uint32) as int32) by { solve() using {
                at(region(10).entry, 0 < __rust_iter_3_5_remaining);
                at(region(10).entry, __rust_iter_3_5_remaining <= ((bytes.len() as uint32) as int32));
                0 <= ((bytes.len() as uint32) as int32); 1000 >= ((bytes.len() as uint32) as int32);
            } }
            have 0 <= (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) by {
                solve() using {
                    at(region(10).entry, 0 < __rust_iter_3_5_remaining);
                    at(region(10).entry, __rust_iter_3_5_remaining <= ((bytes.len() as uint32) as int32));
                    0 <= ((bytes.len() as uint32) as int32); 1000 >= ((bytes.len() as uint32) as int32);
                }
            }
            have 0 <= ((bytes.len() as uint32) as int32) by { solve(); }
            have (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) == at(region(10).entry, ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) by {
                solve() using {
                    at(region(10).entry, 0 < __rust_iter_3_5_remaining);
                    at(region(10).entry, __rust_iter_3_5_remaining <= ((bytes.len() as uint32) as int32));
                    0 <= ((bytes.len() as uint32) as int32); 1000 >= ((bytes.len() as uint32) as int32);
                }
            }
            have __rust_iter_3_5_item == bytes + at(region(10).entry, ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) by { solve(); }
            have __rust_iter_3_5_item == bytes + (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) by {
                rewrite((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) == at(region(10).entry, ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining));
                solve();
            }
            step_until(region(23));
            have bytes + (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) == __rust_iter_3_5_item by { solve(); }
            have 0 <= __rust_checked_1 and 255 >= __rust_checked_1 by { solve(); }
            have 0 <= (load_uint8(__rust_iter_3_5_item) as int32) and 255 >= (load_uint8(__rust_iter_3_5_item) as int32) by { solve(); }
            have ((load_uint8(__rust_iter_3_5_item) as int32)) == (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32) by {
                rewrite(__rust_iter_3_5_item == bytes + (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1));
                solve();
            }
            have 0 <= (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32) and 255 >= (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32) by {
                rewrite(bytes + (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) == __rust_iter_3_5_item); solve();
            }
            have defined(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) by {
                apply(integer::int32_nonnegative_subtract_within_value_is_defined(((bytes.len() as uint32) as int32), __rust_iter_3_5_remaining)) using {
                    0 <= __rust_iter_3_5_remaining;
                    __rust_iter_3_5_remaining <= ((bytes.len() as uint32) as int32);
                } solve();
            }
            have 1 <= ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining by {
                solve() using {
                    at(region(10).entry, 0 < __rust_iter_3_5_remaining);
                    at(region(10).entry, __rust_iter_3_5_remaining <= ((bytes.len() as uint32) as int32));
                    0 <= ((bytes.len() as uint32) as int32); 1000 >= ((bytes.len() as uint32) as int32);
                }
            }
            have defined(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) by {
                apply(integer::int32_nonnegative_subtract_within_value_is_defined(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining, 1)) using {
                    0 <= 1;
                    1 <= ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining;
                } solve();
            }
            have viewable(bytes[0..((bytes.len() as uint32) as int32)]) by {
                transport(at(region(10).entry, viewable(bytes[0..((bytes.len() as uint32) as int32)])), viewable(bytes[0..((bytes.len() as uint32) as int32)])) using {
                    at(region(10).entry, viewable(bytes[0..((bytes.len() as uint32) as int32)]));
                    0 <= ((bytes.len() as uint32) as int32);
                }
            }
            have defined(bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)]) by {
                transport(viewable(bytes[0..((bytes.len() as uint32) as int32)]), defined(bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)])) using {
                    viewable(bytes[0..((bytes.len() as uint32) as int32)]);
                    defined(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1);
                    0 <= ((bytes.len() as uint32) as int32);
                    0 <= (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1);
                    (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) < ((bytes.len() as uint32) as int32);
                }
            }
            have 0 <= to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) by {
                apply(integer::int32_less_equal_to_integer(0, (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32))) using {
                    0 <= (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32);
                }
            }
            have to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) <= 255 by {
                apply(integer::int32_less_equal_to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32), 255)) using {
                    255 >= (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32);
                }
            }
            have to_integer(total) + to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) >= -2147483648 by {
                solve() using {
                    0 <= to_integer(total);
                    0 <= to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32));
                }
            }
            have to_integer(total) + to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) <= 2147483647 by {
                solve() using {
                    to_integer(total) <= 255000;
                    to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) <= 255;
                }
            }
            have defined(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) by {
                apply(integer::int32_add_defined_by_integer_bounds(total, (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32))) using {
                    to_integer(total) + to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) >= -2147483648;
                    to_integer(total) + to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) <= 2147483647;
                } solve();
            }
            have to_integer(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) == to_integer(total) + to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) by {
                apply(integer::int32_add_to_integer(total, (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32))) using {
                    defined(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32));
                }
            }
            have 1000 >= (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) by {
                solve() using {
                    at(region(10).entry, 0 < __rust_iter_3_5_remaining);
                    at(region(10).entry, __rust_iter_3_5_remaining <= ((bytes.len() as uint32) as int32));
                    0 <= ((bytes.len() as uint32) as int32); 1000 >= ((bytes.len() as uint32) as int32);
                }
            }
            have to_integer(total) == prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)) by {
                rewrite((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) == at(region(10).entry, ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining)); solve();
            }
            have to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)) == at(region(10).entry, to_integer(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining)) by {
                rewrite((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) == at(region(10).entry, ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining)); solve();
            }
            have to_integer(total) <= 255 * to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)) by {
                solve() using {
                    at(region(10).entry, to_integer(total) <= 255 * to_integer(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining));
                    to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)) == at(region(10).entry, to_integer(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining));
                }
            }
            have ((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)) < 2147483647 by {
                apply(int32_le_lt_transitive((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1), 1000, 2147483647)) using {
                    1000 >= (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1);
                    1000 < 2147483647;
                }
            }
            have prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1) == prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)) + to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) by {
                peel(prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1)) using {
                    0 <= (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1);
                    ((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)) < 2147483647;
                }
                solve();
            }
            have to_integer(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) == prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1) by {
                solve() using {
                    to_integer(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) == to_integer(total) + to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32));
                    to_integer(total) == prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1));
                    prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1) == prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)) + to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32));
                }
            }
            have defined((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1) by {
                apply(integer::int32_increment_below_max_is_defined((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1))) using {
                    ((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)) < 2147483647;
                } solve();
            }
            have to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1) == to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)) + 1 by {
                apply(integer::int32_add_to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1), 1)) using {
                    defined((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1);
                }
            }
            have 0 <= to_integer(total) + to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) by {
                solve() using {
                    0 <= to_integer(total);
                    0 <= to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32));
                }
            }
            have 0 <= to_integer(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) by {
                solve() using {
                    0 <= to_integer(total) + to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32));
                    to_integer(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) == to_integer(total) + to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32));
                }
            }
            have to_integer(total) + to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) <= 255 * (to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)) + 1) by {
                solve() using {
                    to_integer(total) <= 255 * to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1));
                    to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) <= 255;
                }
            }
            have to_integer(total) + to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) <= 255 * to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1) by {
                solve() using {
                    to_integer(total) + to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) <= 255 * (to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)) + 1);
                    to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1) == to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)) + 1;
                }
            }
            have to_integer(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) <= 255 * to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1) by {
                solve() using {
                    to_integer(total) + to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) <= 255 * to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1);
                    to_integer(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) == to_integer(total) + to_integer((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32));
                }
            }
            have (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) == (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1 by {
                solve() using {
                    at(region(10).entry, 0 < __rust_iter_3_5_remaining);
                    at(region(10).entry, __rust_iter_3_5_remaining <= ((bytes.len() as uint32) as int32));
                    0 <= ((bytes.len() as uint32) as int32); 1000 >= ((bytes.len() as uint32) as int32);
                }
            }
            have at(region(10).entry, ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) < 2147483647 by {
                apply(int32_le_lt_transitive(at(region(10).entry, ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining), 1000, 2147483647)) using {
                    at(region(10).entry, 1000 >= (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining));
                    1000 < 2147483647;
                }
            }
            have __rust_iter_3_5_item + 1 == bytes + (at(region(10).entry, ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) + 1) by {
                solve() using {
                    __rust_iter_3_5_item == bytes + at(region(10).entry, ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining);
                    at(region(10).entry, ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) < 2147483647;
                }
            }
            have (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) == at(region(10).entry, ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) + 1 by {
                solve() using {
                    at(region(10).entry, 0 < __rust_iter_3_5_remaining);
                    at(region(10).entry, __rust_iter_3_5_remaining <= ((bytes.len() as uint32) as int32));
                    0 <= ((bytes.len() as uint32) as int32); 1000 >= ((bytes.len() as uint32) as int32);
                }
            }
            have __rust_iter_3_5_cursor == bytes + (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) by {
                rewrite((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) == at(region(10).entry, ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) + 1);
                solve();
            }
            have to_integer(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) == to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1) by {
                rewrite((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) == (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1); solve();
            }
            have to_integer(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) <= 255 * to_integer(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) by {
                solve() using {
                    to_integer(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) <= 255 * to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1);
                    to_integer(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) == to_integer((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1);
                }
            }
            have prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1) == prefix(bytes, ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) by {
                rewrite((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) == (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1); solve();
            }
            have ((bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) == (load_uint8(__rust_iter_3_5_item) as int32) by { solve(); }
            have defined(total + (load_uint8(__rust_iter_3_5_item) as int32)) by {
                rewrite(((load_uint8(__rust_iter_3_5_item) as int32)) == (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)); solve();
            }
            // Connect Rust's captured addition operands to the mathematical sum.
            have __rust_checked_1 == (load_uint8(__rust_iter_3_5_item) as int32) by { solve(); }
            have __rust_checked_0 == total by { solve(); }
            have defined(__rust_checked_0 + __rust_checked_1) by { solve(); }
            have to_integer(__rust_checked_0 + __rust_checked_1) == to_integer(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) by {
                rewrite(__rust_checked_0 == total);
                rewrite(__rust_checked_1 == (load_uint8(__rust_iter_3_5_item) as int32));
                rewrite(((load_uint8(__rust_iter_3_5_item) as int32)) == (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)); solve();
            }
            have 0 <= to_integer(__rust_checked_0 + __rust_checked_1) by {
                solve() using {
                    to_integer(__rust_checked_0 + __rust_checked_1) == to_integer(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32));
                    0 <= to_integer(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32));
                }
            }
            have to_integer(__rust_checked_0 + __rust_checked_1) <= 255 * to_integer(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) by {
                solve() using {
                    to_integer(__rust_checked_0 + __rust_checked_1) == to_integer(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32));
                    to_integer(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) <= 255 * to_integer(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining);
                }
            }
            have to_integer(__rust_checked_0 + __rust_checked_1) == prefix(bytes, ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) by {
                solve() using {
                    to_integer(__rust_checked_0 + __rust_checked_1) == to_integer(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32));
                    to_integer(total + (bytes[(((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1)] as int32)) == prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1);
                    prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining - 1) + 1) == prefix(bytes, ((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining);
                }
            }
            step();
            have viewable(bytes[0..((bytes.len() as uint32) as int32)]) by {
                transport(at(region(23).entry, viewable(bytes[0..((bytes.len() as uint32) as int32)])), viewable(bytes[0..((bytes.len() as uint32) as int32)])) using {
                    at(region(23).entry, viewable(bytes[0..((bytes.len() as uint32) as int32)]));
                    0 <= ((bytes.len() as uint32) as int32);
                }
            }
            close_invariants();
        }
    }
    have __rust_iter_3_5_remaining == 0 by { solve(); }
    have (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) == ((bytes.len() as uint32) as int32) by { solve(); }
    have prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining)) == prefix(bytes, ((bytes.len() as uint32) as int32)) by {
        rewrite((((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining) == ((bytes.len() as uint32) as int32)); solve();
    }
    have to_integer(total) == prefix(bytes, ((bytes.len() as uint32) as int32)) by {
        solve() using {
            to_integer(total) == prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining));
            prefix(bytes, (((bytes.len() as uint32) as int32) - __rust_iter_3_5_remaining)) == prefix(bytes, ((bytes.len() as uint32) as int32));
        }
    }
    step_until(function.exit);
    solve();
}

import click::integer;
