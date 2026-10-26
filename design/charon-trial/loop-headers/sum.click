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
    step_until(region(7));
    have prefix(bytes, ((i as uint32) as int32)) == 0 by {
        peel(prefix(bytes, ((i as uint32) as int32))) using {
            0 >= ((i as uint32) as int32);
        } solve();
    }
    have to_integer(total) == 0 by {
        solve();
    }
    have to_integer(total) == prefix(bytes, ((i as uint32) as int32)) by {
        solve() using {
            to_integer(total) == 0;
            prefix(bytes, ((i as uint32) as int32)) == 0;
        }
    }
    loop {
        decreases bytes.len() - i;
        views bytes[0..((bytes.len() as uint32) as int32)];
        invariant i <= bytes.len();
        invariant bytes.len() <= 1000u64;
        invariant 0 <= ((i as uint32) as int32) and 1000 >= ((i as uint32) as int32);
        invariant 0 <= to_integer(total) and to_integer(total) <= 255 * to_integer(((i as uint32) as int32));
        invariant to_integer(total) == prefix(bytes, ((i as uint32) as int32));
        preserve by {
            have bytes.len() <= 2147483647u64 by {
                normalize() using {
                    bytes.len() <= 1000u64;
                }
            }
            have 0 <= to_integer(((i as uint32) as int32)) by {
                apply(integer::int32_less_equal_to_integer(0, ((i as uint32) as int32))) using {
                    0 <= ((i as uint32) as int32);
                }
            }
            have to_integer(((i as uint32) as int32)) <= 1000 by {
                apply(integer::int32_less_equal_to_integer(((i as uint32) as int32), 1000)) using {
                    1000 >= ((i as uint32) as int32);
                }
            }
            have to_integer(total) <= 255000 by {
                solve() using {
                    to_integer(total) <= 255 * to_integer(((i as uint32) as int32));
                    to_integer(((i as uint32) as int32)) <= 1000;
                }
            }
            step_until(region(18));
            have (((i as uint32) as int32)) < ((bytes.len() as uint32) as int32) by {
                solve() using {
                    i < bytes.len();
                    bytes.len() <= 2147483647u64;
                }
            }
            have 0 <= ((i as uint32) as int32) by {
                solve();
            }
            have 0 <= ((bytes.len() as uint32) as int32) by {
                solve();
            }
            have 0 <= (bytes[((i as uint32) as int32)] as int32) and 255 >= (bytes[((i as uint32) as int32)] as int32) by {
                solve();
            }
            have defined(bytes[((i as uint32) as int32)]) by {
                transport(at(function.entry, viewable(bytes[0..((bytes.len() as uint32) as int32)])), defined(bytes[((i as uint32) as int32)])) using {
                    at(function.entry, viewable(bytes[0..((bytes.len() as uint32) as int32)]));
                    0 <= ((bytes.len() as uint32) as int32);
                    0 <= ((i as uint32) as int32);
                    (((i as uint32) as int32)) < ((bytes.len() as uint32) as int32);
                }
            }
            have 0 <= to_integer((bytes[((i as uint32) as int32)] as int32)) by {
                apply(integer::int32_less_equal_to_integer(0, (bytes[((i as uint32) as int32)] as int32))) using {
                    0 <= (bytes[((i as uint32) as int32)] as int32);
                }
            }
            have to_integer((bytes[((i as uint32) as int32)] as int32)) <= 255 by {
                apply(integer::int32_less_equal_to_integer((bytes[((i as uint32) as int32)] as int32), 255)) using {
                    255 >= (bytes[((i as uint32) as int32)] as int32);
                }
            }
            have to_integer(total) + to_integer((bytes[((i as uint32) as int32)] as int32)) >= -2147483648 by {
                solve() using {
                    0 <= to_integer(total);
                    0 <= to_integer((bytes[((i as uint32) as int32)] as int32));
                }
            }
            have to_integer(total) + to_integer((bytes[((i as uint32) as int32)] as int32)) <= 2147483647 by {
                solve() using {
                    to_integer(total) <= 255000;
                    to_integer((bytes[((i as uint32) as int32)] as int32)) <= 255;
                }
            }
            have defined(total + (bytes[((i as uint32) as int32)] as int32)) by {
                apply(integer::int32_add_defined_by_integer_bounds(total, (bytes[((i as uint32) as int32)] as int32))) using {
                    to_integer(total) + to_integer((bytes[((i as uint32) as int32)] as int32)) >= -2147483648;
                    to_integer(total) + to_integer((bytes[((i as uint32) as int32)] as int32)) <= 2147483647;
                } solve();
            }
            have to_integer(total + (bytes[((i as uint32) as int32)] as int32)) == to_integer(total) + to_integer((bytes[((i as uint32) as int32)] as int32)) by {
                apply(integer::int32_add_to_integer(total, (bytes[((i as uint32) as int32)] as int32))) using {
                    defined(total + (bytes[((i as uint32) as int32)] as int32));
                }
            }
            have (((i as uint32) as int32)) < 2147483647 by {
                apply(int32_le_lt_transitive(((i as uint32) as int32), 1000, 2147483647)) using {
                    1000 >= ((i as uint32) as int32);
                    1000 < 2147483647;
                }
            }
            have prefix(bytes, ((i as uint32) as int32) + 1) == prefix(bytes, ((i as uint32) as int32)) + to_integer((bytes[((i as uint32) as int32)] as int32)) by {
                peel(prefix(bytes, ((i as uint32) as int32) + 1)) using {
                    0 <= ((i as uint32) as int32);
                    (((i as uint32) as int32)) < 2147483647;
                }
                solve();
            }
            have to_integer(total + (bytes[((i as uint32) as int32)] as int32)) == prefix(bytes, ((i as uint32) as int32) + 1) by {
                solve() using {
                    to_integer(total + (bytes[((i as uint32) as int32)] as int32)) == to_integer(total) + to_integer((bytes[((i as uint32) as int32)] as int32));
                    to_integer(total) == prefix(bytes, ((i as uint32) as int32));
                    prefix(bytes, ((i as uint32) as int32) + 1) == prefix(bytes, ((i as uint32) as int32)) + to_integer((bytes[((i as uint32) as int32)] as int32));
                }
            }
            have defined(((i as uint32) as int32) + 1) by {
                apply(integer::int32_increment_below_max_is_defined(((i as uint32) as int32))) using {
                    (((i as uint32) as int32)) < 2147483647;
                }
            }
            have to_integer(((i as uint32) as int32) + 1) == to_integer(((i as uint32) as int32)) + 1 by {
                apply(integer::int32_add_to_integer(((i as uint32) as int32), 1)) using {
                    defined(((i as uint32) as int32) + 1);
                }
            }
            have 0 <= to_integer(total) + to_integer((bytes[((i as uint32) as int32)] as int32)) by {
                solve() using {
                    0 <= to_integer(total);
                    0 <= to_integer((bytes[((i as uint32) as int32)] as int32));
                }
            }
            have 0 <= to_integer(total + (bytes[((i as uint32) as int32)] as int32)) by {
                solve() using {
                    0 <= to_integer(total) + to_integer((bytes[((i as uint32) as int32)] as int32));
                    to_integer(total + (bytes[((i as uint32) as int32)] as int32)) == to_integer(total) + to_integer((bytes[((i as uint32) as int32)] as int32));
                }
            }
            have to_integer(total) + to_integer((bytes[((i as uint32) as int32)] as int32)) <= 255 * (to_integer(((i as uint32) as int32)) + 1) by {
                solve() using {
                    to_integer(total) <= 255 * to_integer(((i as uint32) as int32));
                    to_integer((bytes[((i as uint32) as int32)] as int32)) <= 255;
                }
            }
            have to_integer(total) + to_integer((bytes[((i as uint32) as int32)] as int32)) <= 255 * to_integer(((i as uint32) as int32) + 1) by {
                solve() using {
                    to_integer(total) + to_integer((bytes[((i as uint32) as int32)] as int32)) <= 255 * (to_integer(((i as uint32) as int32)) + 1);
                    to_integer(((i as uint32) as int32) + 1) == to_integer(((i as uint32) as int32)) + 1;
                }
            }
            have to_integer(total + (bytes[((i as uint32) as int32)] as int32)) <= 255 * to_integer(((i as uint32) as int32) + 1) by {
                solve() using {
                    to_integer(total) + to_integer((bytes[((i as uint32) as int32)] as int32)) <= 255 * to_integer(((i as uint32) as int32) + 1);
                    to_integer(total + (bytes[((i as uint32) as int32)] as int32)) == to_integer(total) + to_integer((bytes[((i as uint32) as int32)] as int32));
                }
            }
            step_until(region(26));
            step();
            have i <= bytes.len() by {
                solve();
            }
            have i <= 1000u64 by {
                normalize() using {
                    i <= bytes.len();
                    bytes.len() <= 1000u64;
                }
            }
            have i <= 2147483647u64 by {
                normalize() using {
                    i <= 1000u64;
                }
            }
            have 0 <= ((i as uint32) as int32) by {
                normalize() using {
                    i <= 2147483647u64;
                }
            }
            have 1000 >= ((i as uint32) as int32) by {
                normalize() using {
                    i <= 1000u64;
                }
            }
            close_invariants();
        }
    }
    have i == bytes.len() by {
        solve() using {
            i <= bytes.len();
            not i < bytes.len();
        }
    }
    have (((i as uint32) as int32)) == ((bytes.len() as uint32) as int32) by {
        normalize() using {
            i == bytes.len();
        }
    }
    have prefix(bytes, ((i as uint32) as int32)) == prefix(bytes, ((bytes.len() as uint32) as int32)) by {
        rewrite((((i as uint32) as int32)) == ((bytes.len() as uint32) as int32));
        solve();
    }
    have to_integer(total) == prefix(bytes, ((bytes.len() as uint32) as int32)) by {
        solve() using {
            to_integer(total) == prefix(bytes, ((i as uint32) as int32));
            prefix(bytes, ((i as uint32) as int32)) == prefix(bytes, ((bytes.len() as uint32) as int32));
        }
    }
    step_until(function.exit);
    solve();
}

import click::integer;
