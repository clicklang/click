// Linux `string_get_size` (lib/string_helpers.c, v7.3), unchanged, for
// both unit systems (powers of 1000 and of 1024) and every flag combination.
// The proof uses Click's default x86_64-unknown-linux-gnu kernel target.
//
// It proves the call is free of undefined behavior and that `buf` holds a
// terminated string: the result, the number of characters the format
// produces, is never negative, and the terminator follows the output when it
// fits and ends the buffer when it does not.
import click::cstr;
import click::format;
import click::integer;
verifying "string_get_size.c";

// The length of the fraction `tmp` holds after the `if (j)` block: empty when
// no digits of precision follow, else the point and `j` digits.
function tmp_len(j: int32) -> uint64 {
    if j == 0 { 0u64 } else { (uint64) j + 1u64 }
}

// The division bounds that hold for either divisor, 1000 or 1024. The loops
// state their bounds in Integer form, `x * 1000^k <= UINT64_MAX`, so each
// step is linear and needs no rounding.
theorem left_multiply_order(factor: Integer, a: Integer, b: Integer) {
    requires a <= b;
    requires 0 <= factor;
    ensures factor * a <= factor * b by {
        arithmetic_certificate rules {
            premise 0: a <= b => a <= b;
            premise 1: 0 <= factor => 0 <= factor;
            integer_multiply_order bounds [0, 1] => factor * a <= factor * b;
            conclusion 0;
        }
    }
}

theorem kilo_quotient(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 <= n;
    requires 1000 <= d;
    requires d <= 1024;
    ensures truncating_quotient(n, d) * 1000 <= n
        and n < truncating_quotient(n, d) * 1024 + 1024 by {
    have 1 <= d by { arithmetic() using { 1000 <= d; }; }
    have 0 < d by { arithmetic() using { 1000 <= d; }; }
    have 0 * d <= n by { arithmetic() using { 0 <= n; }; }
    apply(integer::positive_divisor_quotient_lower(n, d, 0));
    apply(integer::truncation_identity(n, d));
    apply(integer::nonnegative_dividend_remainder(n, d));
    apply(integer::positive_divisor_remainder_upper(n, d));
    apply(left_multiply_order(truncating_quotient(n, d), 1000, d));
    apply(left_multiply_order(truncating_quotient(n, d), d, 1024));
    have truncating_quotient(n, d) * 1000 <= n by { arithmetic() using {
        truncating_quotient(n, d) * 1000 <= truncating_quotient(n, d) * d;
        n == truncating_quotient(n, d) * d + truncating_remainder(n, d);
        0 <= truncating_remainder(n, d);
    }; }
    have n < truncating_quotient(n, d) * 1024 + 1024 by { arithmetic() using {
        truncating_quotient(n, d) * d <= truncating_quotient(n, d) * 1024;
        n == truncating_quotient(n, d) * d + truncating_remainder(n, d);
        truncating_remainder(n, d) <= d - 1;
        d <= 1024;
    }; }
    solve();
    }
}

theorem kilo_divide(x: uint64, d: uint32) {
    requires 1000u32 <= d;
    requires d <= 1024u32;
    ensures to_integer(x / (uint64) d) * 1000 <= to_integer(x)
        and to_integer(x) < to_integer(x / (uint64) d) * 1024 + 1024 by {
        have (uint64) d != 0u64 by { auto(); }
        have 1000 <= to_integer((uint64) d) by { auto(); }
        have to_integer((uint64) d) <= 1024 by { auto(); }
        have to_integer((uint64) d) != 0 by { auto(); }
        have 0 <= to_integer(x) by { auto(); }
        apply(integer::uint64_divide_to_integer(x, (uint64) d));
        apply(kilo_quotient(to_integer(x), to_integer((uint64) d)));
        rewrite(to_integer(x / (uint64) d) == truncating_quotient(to_integer(x), to_integer((uint64) d)));
        assumption();
    }
}

int32 string_get_size(uint64 size, uint64 blk_size, uint32 units, char buf[], int32 len) {
    requires 9 <= len;
    owns buf[0..(uint64) len];
    ensures 0 <= result;
    ensures (uint64) result < (uint64) len implies buf[(uint64) result] == 0u8;
    ensures (uint64) result >= (uint64) len implies buf[(uint64) len - 1u64] == 0u8;
} by {
// `size` is zero: both early exits print `0`, an empty fraction, and the
// unit for `i == 0`.
    if blk_size == 0u64 {
        execute_until(region(77));
        have format::decimal_length((uint64)(uint32) size) <= 20u64 by { unfold(format::decimal_length((uint64)(uint32) size)); solve(); }
        have (uint64) len != 0u64 by { auto(); }
        have forall (k: uint64) { 0u64 <= k and k < 0u64 implies tmp[k] != 0u8 } by {
            intro();
            intro();
            have false by { arithmetic() using { k < 0u64; }; }
            contradiction(false);
        }
        have forall (k: uint64) { 0u64 <= k and k < 0u64 + 1u64 implies defined(tmp[k]) } by { enumerate(); }
        step();
        if (units & 1u32) == 1u32 {
            step();
            step();
            if (units & 1073741824u32) != 0u32 {
                if (units & 2147483648u32) != 0u32 {
                    step(snprintf, { n1: 0u64 });
                    execute();
                    solve();
                } else {
                    step(snprintf, { n1: 0u64 });
                    execute();
                    solve();
                }
            } else {
                if (units & 2147483648u32) != 0u32 {
                    step(snprintf, { n1: 0u64 });
                    execute();
                    solve();
                } else {
                    step(snprintf, { n1: 0u64 });
                    execute();
                    solve();
                }
            }
        } else {
            step();
            step();
            if (units & 1073741824u32) != 0u32 {
                if (units & 2147483648u32) != 0u32 {
                    step(snprintf, { n1: 0u64 });
                    execute();
                    solve();
                } else {
                    step(snprintf, { n1: 0u64 });
                    execute();
                    solve();
                }
            } else {
                if (units & 2147483648u32) != 0u32 {
                    step(snprintf, { n1: 0u64 });
                    execute();
                    solve();
                } else {
                    step(snprintf, { n1: 0u64 });
                    execute();
                    solve();
                }
            }
        }
    } else {
        if size == 0u64 {
            execute_until(region(77));
            have format::decimal_length((uint64)(uint32) size) <= 20u64 by { unfold(format::decimal_length((uint64)(uint32) size)); solve(); }
            have (uint64) len != 0u64 by { auto(); }
            have forall (k: uint64) { 0u64 <= k and k < 0u64 implies tmp[k] != 0u8 } by {
                intro();
                intro();
                have false by { arithmetic() using { k < 0u64; }; }
                contradiction(false);
            }
            have forall (k: uint64) { 0u64 <= k and k < 0u64 + 1u64 implies defined(tmp[k]) } by { enumerate(); }
            step();
            if (units & 1u32) == 1u32 {
                step();
                step();
                if (units & 1073741824u32) != 0u32 {
                    if (units & 2147483648u32) != 0u32 {
                        step(snprintf, { n1: 0u64 });
                        execute();
                        solve();
                    } else {
                        step(snprintf, { n1: 0u64 });
                        execute();
                        solve();
                    }
                } else {
                    if (units & 2147483648u32) != 0u32 {
                        step(snprintf, { n1: 0u64 });
                        execute();
                        solve();
                    } else {
                        step(snprintf, { n1: 0u64 });
                        execute();
                        solve();
                    }
                }
            } else {
                step();
                step();
                if (units & 1073741824u32) != 0u32 {
                    if (units & 2147483648u32) != 0u32 {
                        step(snprintf, { n1: 0u64 });
                        execute();
                        solve();
                    } else {
                        step(snprintf, { n1: 0u64 });
                        execute();
                        solve();
                    }
                } else {
                    if (units & 2147483648u32) != 0u32 {
                        step(snprintf, { n1: 0u64 });
                        execute();
                        solve();
                    } else {
                        step(snprintf, { n1: 0u64 });
                        execute();
                        solve();
                    }
                }
            }
        } else {
// Napier's reduction: each loop divides by `divisor[units_base]`, read once
// per iteration through a join that keeps only `1000 <= __base <= 1024`.
            execute_until(loop(0));
            loop {
                decreases blk_size;
                invariant 1u64 <= blk_size;
                invariant 0 <= i and i <= 4;
                invariant i == 1 implies to_integer(blk_size) * 1000 <= 18446744073709551615;
                invariant i == 2 implies to_integer(blk_size) * 1000000 <= 18446744073709551615;
                invariant i == 3 implies to_integer(blk_size) * 1000000000 <= 18446744073709551615;
                invariant i == 4 implies to_integer(blk_size) * 1000000000000 <= 18446744073709551615;
                initialize by { auto(); }
                preserve by {
                    mark head;
                    step();
                    step();
                    step();
                    if (units & 1u32) == 1u32 ensuring {
                        fact 1000u32 <= __base;
                        fact __base <= 1024u32;
                    } then {
                        step();
                    } else {
                        step();
                    }
                    mark div;
                    apply(kilo_divide(at(head, blk_size), at(div, __base)));
                    execute_until(back_edge());
                    have 4294967296 <= to_integer(at(head, blk_size)) by { auto(); }
                    have 1u64 <= blk_size by { auto(); }
                    have blk_size < at(head, blk_size) by { auto(); }
                    have at(head, i) < 4 by {
                        if at(head, i) < 4 {
                            assumption();
                        } else {
                            have at(head, i) == 4 by { auto(); }
                            have to_integer(at(head, blk_size)) * 1000000000000 <= 18446744073709551615 by { solve(); }
                            have false by { arithmetic() using {
                                to_integer(at(head, blk_size)) * 1000000000000 <= 18446744073709551615;
                                4294967296 <= to_integer(at(head, blk_size));
                            }; }
                            contradiction(false);
                        }
                    }
                    have i == 1 implies to_integer(blk_size) * 1000 <= 18446744073709551615 by { auto(); }
                    have i == 2 implies to_integer(blk_size) * 1000000 <= 18446744073709551615 by {
                        intro();
                        have at(head, i) == 1 by { auto(); }
                        have to_integer(at(head, blk_size)) * 1000 <= 18446744073709551615 by { solve(); }
                        have to_integer(blk_size) * 1000000 <= 18446744073709551615 by { arithmetic() using {
                            to_integer(at(head, blk_size) / (uint64)at(div, __base)) * 1000 <= to_integer(at(head, blk_size));
                            to_integer(at(head, blk_size)) * 1000 <= 18446744073709551615;
                        }; }
                        assumption();
                    }
                    have i == 3 implies to_integer(blk_size) * 1000000000 <= 18446744073709551615 by {
                        intro();
                        have at(head, i) == 2 by { auto(); }
                        have to_integer(at(head, blk_size)) * 1000000 <= 18446744073709551615 by { solve(); }
                        have to_integer(blk_size) * 1000000000 <= 18446744073709551615 by { arithmetic() using {
                            to_integer(at(head, blk_size) / (uint64)at(div, __base)) * 1000 <= to_integer(at(head, blk_size));
                            to_integer(at(head, blk_size)) * 1000000 <= 18446744073709551615;
                        }; }
                        assumption();
                    }
                    have i == 4 implies to_integer(blk_size) * 1000000000000 <= 18446744073709551615 by {
                        intro();
                        have at(head, i) == 3 by { auto(); }
                        have to_integer(at(head, blk_size)) * 1000000000 <= 18446744073709551615 by { solve(); }
                        have to_integer(blk_size) * 1000000000000 <= 18446744073709551615 by { arithmetic() using {
                            to_integer(at(head, blk_size) / (uint64)at(div, __base)) * 1000 <= to_integer(at(head, blk_size));
                            to_integer(at(head, blk_size)) * 1000000000 <= 18446744073709551615;
                        }; }
                        assumption();
                    }
                    close_invariants() by { solve(); }
                }
            }
            execute_until(loop(1));
            have blk_size < 4294967296u64 by { auto(); }
            loop {
                decreases size;
                invariant 1u64 <= size;
                invariant at(loop(1).entry, i) <= i and i <= at(loop(1).entry, i) + 4;
                invariant 0 <= at(loop(1).entry, i) and at(loop(1).entry, i) <= 4;
                invariant 1u64 <= blk_size and blk_size < 4294967296u64;
                invariant i == at(loop(1).entry, i) + 1 implies to_integer(size) * 1000 <= 18446744073709551615;
                invariant i == at(loop(1).entry, i) + 2 implies to_integer(size) * 1000000 <= 18446744073709551615;
                invariant i == at(loop(1).entry, i) + 3 implies to_integer(size) * 1000000000 <= 18446744073709551615;
                invariant i == at(loop(1).entry, i) + 4 implies to_integer(size) * 1000000000000 <= 18446744073709551615;
                initialize by { auto(); }
                preserve by {
                    have i <= 8 by { auto(); }
                    mark head;
                    step();
                    step();
                    step();
                    if (units & 1u32) == 1u32 ensuring {
                        fact 1000u32 <= __base;
                        fact __base <= 1024u32;
                    } then {
                        step();
                    } else {
                        step();
                    }
                    mark div;
                    apply(kilo_divide(at(head, size), at(div, __base)));
                    execute_until(back_edge());
                    have 4294967296 <= to_integer(at(head, size)) by { auto(); }
                    have 1u64 <= size by { auto(); }
                    have size < at(head, size) by { auto(); }
                    have at(head, i) < at(loop(1).entry, i) + 4 by {
                        if at(head, i) < at(loop(1).entry, i) + 4 {
                            assumption();
                        } else {
                            have at(head, i) == at(loop(1).entry, i) + 4 by { auto(); }
                            have to_integer(at(head, size)) * 1000000000000 <= 18446744073709551615 by { solve(); }
                            have false by { arithmetic() using {
                                to_integer(at(head, size)) * 1000000000000 <= 18446744073709551615;
                                4294967296 <= to_integer(at(head, size));
                            }; }
                            contradiction(false);
                        }
                    }
                    have i == at(loop(1).entry, i) + 1 implies to_integer(size) * 1000 <= 18446744073709551615 by { auto(); }
                    have i == at(loop(1).entry, i) + 2 implies to_integer(size) * 1000000 <= 18446744073709551615 by {
                        intro();
                        have at(head, i) == at(loop(1).entry, i) + 1 by { auto(); }
                        have to_integer(at(head, size)) * 1000 <= 18446744073709551615 by { solve(); }
                        have to_integer(size) * 1000000 <= 18446744073709551615 by { arithmetic() using {
                            to_integer(at(head, size) / (uint64)at(div, __base)) * 1000 <= to_integer(at(head, size));
                            to_integer(at(head, size)) * 1000 <= 18446744073709551615;
                        }; }
                        assumption();
                    }
                    have i == at(loop(1).entry, i) + 3 implies to_integer(size) * 1000000000 <= 18446744073709551615 by {
                        intro();
                        have at(head, i) == at(loop(1).entry, i) + 2 by { auto(); }
                        have to_integer(at(head, size)) * 1000000 <= 18446744073709551615 by { solve(); }
                        have to_integer(size) * 1000000000 <= 18446744073709551615 by { arithmetic() using {
                            to_integer(at(head, size) / (uint64)at(div, __base)) * 1000 <= to_integer(at(head, size));
                            to_integer(at(head, size)) * 1000000 <= 18446744073709551615;
                        }; }
                        assumption();
                    }
                    have i == at(loop(1).entry, i) + 4 implies to_integer(size) * 1000000000000 <= 18446744073709551615 by {
                        intro();
                        have at(head, i) == at(loop(1).entry, i) + 3 by { auto(); }
                        have to_integer(at(head, size)) * 1000000000 <= 18446744073709551615 by { solve(); }
                        have to_integer(size) * 1000000000000 <= 18446744073709551615 by { arithmetic() using {
                            to_integer(at(head, size) / (uint64)at(div, __base)) * 1000 <= to_integer(at(head, size));
                            to_integer(at(head, size)) * 1000000000 <= 18446744073709551615;
                        }; }
                        assumption();
                    }
                    close_invariants() by { solve(); }
                }
            }
            have size < 4294967296u64 by { auto(); }
            have to_integer(size) <= 4294967295 by { auto(); }
            have to_integer(blk_size) <= 4294967295 by { auto(); }
            have 1 <= to_integer(blk_size) by { auto(); }
            have 1 <= to_integer(size) by { auto(); }
            have 0 <= to_integer(blk_size) by { auto(); }
            have 0 <= to_integer(size) by { auto(); }
            apply(integer::multiply_order_nonnegative(to_integer(size), 4294967295, to_integer(blk_size)));
            have 4294967295 * to_integer(blk_size) <= 18446744065119617025 by { auto(); }
            have to_integer(size) * to_integer(blk_size) <= 18446744073709551615 by { auto(); }
            apply(integer::uint64_multiply_to_integer(size, blk_size));
            apply(integer::multiply_order_nonnegative(1, to_integer(size), to_integer(blk_size)));
            have 1 <= to_integer(size * blk_size) by { auto(); }
            have 1u64 <= size * blk_size by { auto(); }
// `size *= blk_size` cannot wrap: both factors are below 2^32.
            step();
            execute_until(loop(2));
            loop {
                decreases size;
                invariant 1u64 <= size;
                invariant remainder <= 1023u32;
                invariant (units & 1u32) != 1u32 implies remainder <= 999u32;
                invariant at(loop(2).entry, i) <= i and i <= at(loop(2).entry, i) + 6;
                invariant 0 <= at(loop(2).entry, i) and at(loop(2).entry, i) <= 8;
                invariant i == at(loop(2).entry, i) + 1 implies to_integer(size) * 1000 <= 18446744073709551615;
                invariant i == at(loop(2).entry, i) + 2 implies to_integer(size) * 1000000 <= 18446744073709551615;
                invariant i == at(loop(2).entry, i) + 3 implies to_integer(size) * 1000000000 <= 18446744073709551615;
                invariant i == at(loop(2).entry, i) + 4 implies to_integer(size) * 1000000000000 <= 18446744073709551615;
                invariant i == at(loop(2).entry, i) + 5 implies to_integer(size) * 1000000000000000 <= 18446744073709551615;
                invariant i == at(loop(2).entry, i) + 6 implies to_integer(size) * 1000000000000000000 <= 18446744073709551615;
                initialize by { auto(); }
                preserve by {
                    have i <= 14 by { auto(); }
                    mark head;
                    if (units & 1u32) == 1u32 {
                        if 1024u64 <= size {
                            execute_until(back_edge());
                            apply(kilo_divide(at(head, size), 1024u32));
                            have 1024 <= to_integer(at(head, size)) by { auto(); }
                            have 1u64 <= size by { auto(); }
                            have size < at(head, size) by { auto(); }
                            have remainder <= 1023u32 by { auto(); }
                            have (units & 1u32) != 1u32 implies remainder <= 999u32 by { auto(); }
                            have at(head, i) < at(loop(2).entry, i) + 6 by {
                                if at(head, i) < at(loop(2).entry, i) + 6 {
                                    assumption();
                                } else {
                                    have at(head, i) == at(loop(2).entry, i) + 6 by { auto(); }
                                    have to_integer(at(head, size)) * 1000000000000000000 <= 18446744073709551615 by { solve(); }
                                    have false by { arithmetic() using {
                                        to_integer(at(head, size)) * 1000000000000000000 <= 18446744073709551615;
                                        1024 <= to_integer(at(head, size));
                                    }; }
                                    contradiction(false);
                                }
                            }
                            have i == at(loop(2).entry, i) + 1 implies to_integer(size) * 1000 <= 18446744073709551615 by { auto(); }
                            have i == at(loop(2).entry, i) + 2 implies to_integer(size) * 1000000 <= 18446744073709551615 by {
                                intro();
                                have at(head, i) == at(loop(2).entry, i) + 1 by { auto(); }
                                have to_integer(at(head, size)) * 1000 <= 18446744073709551615 by { solve(); }
                                have to_integer(size) * 1000000 <= 18446744073709551615 by { arithmetic() using {
                                    to_integer(at(head, size) / (uint64)1024u32) * 1000 <= to_integer(at(head, size));
                                    to_integer(at(head, size)) * 1000 <= 18446744073709551615;
                                }; }
                                assumption();
                            }
                            have i == at(loop(2).entry, i) + 3 implies to_integer(size) * 1000000000 <= 18446744073709551615 by {
                                intro();
                                have at(head, i) == at(loop(2).entry, i) + 2 by { auto(); }
                                have to_integer(at(head, size)) * 1000000 <= 18446744073709551615 by { solve(); }
                                have to_integer(size) * 1000000000 <= 18446744073709551615 by { arithmetic() using {
                                    to_integer(at(head, size) / (uint64)1024u32) * 1000 <= to_integer(at(head, size));
                                    to_integer(at(head, size)) * 1000000 <= 18446744073709551615;
                                }; }
                                assumption();
                            }
                            have i == at(loop(2).entry, i) + 4 implies to_integer(size) * 1000000000000 <= 18446744073709551615 by {
                                intro();
                                have at(head, i) == at(loop(2).entry, i) + 3 by { auto(); }
                                have to_integer(at(head, size)) * 1000000000 <= 18446744073709551615 by { solve(); }
                                have to_integer(size) * 1000000000000 <= 18446744073709551615 by { arithmetic() using {
                                    to_integer(at(head, size) / (uint64)1024u32) * 1000 <= to_integer(at(head, size));
                                    to_integer(at(head, size)) * 1000000000 <= 18446744073709551615;
                                }; }
                                assumption();
                            }
                            have i == at(loop(2).entry, i) + 5 implies to_integer(size) * 1000000000000000 <= 18446744073709551615 by {
                                intro();
                                have at(head, i) == at(loop(2).entry, i) + 4 by { auto(); }
                                have to_integer(at(head, size)) * 1000000000000 <= 18446744073709551615 by { solve(); }
                                have to_integer(size) * 1000000000000000 <= 18446744073709551615 by { arithmetic() using {
                                    to_integer(at(head, size) / (uint64)1024u32) * 1000 <= to_integer(at(head, size));
                                    to_integer(at(head, size)) * 1000000000000 <= 18446744073709551615;
                                }; }
                                assumption();
                            }
                            have i == at(loop(2).entry, i) + 6 implies to_integer(size) * 1000000000000000000 <= 18446744073709551615 by {
                                intro();
                                have at(head, i) == at(loop(2).entry, i) + 5 by { auto(); }
                                have to_integer(at(head, size)) * 1000000000000000 <= 18446744073709551615 by { solve(); }
                                have to_integer(size) * 1000000000000000000 <= 18446744073709551615 by { arithmetic() using {
                                    to_integer(at(head, size) / (uint64)1024u32) * 1000 <= to_integer(at(head, size));
                                    to_integer(at(head, size)) * 1000000000000000 <= 18446744073709551615;
                                }; }
                                assumption();
                            }
                            close_invariants() by { solve(); }
                        } else {
                            step();
                            step();
                            step();
                        }
                    } else {
                        if 1000u64 <= size {
                            execute_until(back_edge());
                            apply(kilo_divide(at(head, size), 1000u32));
                            have 1000 <= to_integer(at(head, size)) by { auto(); }
                            have 1u64 <= size by { auto(); }
                            have size < at(head, size) by { auto(); }
                            have remainder <= 1023u32 by { auto(); }
                            have remainder <= 999u32 by { auto(); }
                            have (units & 1u32) != 1u32 implies remainder <= 999u32 by { auto(); }
                            have at(head, i) < at(loop(2).entry, i) + 6 by {
                                if at(head, i) < at(loop(2).entry, i) + 6 {
                                    assumption();
                                } else {
                                    have at(head, i) == at(loop(2).entry, i) + 6 by { auto(); }
                                    have to_integer(at(head, size)) * 1000000000000000000 <= 18446744073709551615 by { solve(); }
                                    have false by { arithmetic() using {
                                        to_integer(at(head, size)) * 1000000000000000000 <= 18446744073709551615;
                                        1000 <= to_integer(at(head, size));
                                    }; }
                                    contradiction(false);
                                }
                            }
                            have i == at(loop(2).entry, i) + 1 implies to_integer(size) * 1000 <= 18446744073709551615 by { auto(); }
                            have i == at(loop(2).entry, i) + 2 implies to_integer(size) * 1000000 <= 18446744073709551615 by {
                                intro();
                                have at(head, i) == at(loop(2).entry, i) + 1 by { auto(); }
                                have to_integer(at(head, size)) * 1000 <= 18446744073709551615 by { solve(); }
                                have to_integer(size) * 1000000 <= 18446744073709551615 by { arithmetic() using {
                                    to_integer(at(head, size) / (uint64)1000u32) * 1000 <= to_integer(at(head, size));
                                    to_integer(at(head, size)) * 1000 <= 18446744073709551615;
                                }; }
                                assumption();
                            }
                            have i == at(loop(2).entry, i) + 3 implies to_integer(size) * 1000000000 <= 18446744073709551615 by {
                                intro();
                                have at(head, i) == at(loop(2).entry, i) + 2 by { auto(); }
                                have to_integer(at(head, size)) * 1000000 <= 18446744073709551615 by { solve(); }
                                have to_integer(size) * 1000000000 <= 18446744073709551615 by { arithmetic() using {
                                    to_integer(at(head, size) / (uint64)1000u32) * 1000 <= to_integer(at(head, size));
                                    to_integer(at(head, size)) * 1000000 <= 18446744073709551615;
                                }; }
                                assumption();
                            }
                            have i == at(loop(2).entry, i) + 4 implies to_integer(size) * 1000000000000 <= 18446744073709551615 by {
                                intro();
                                have at(head, i) == at(loop(2).entry, i) + 3 by { auto(); }
                                have to_integer(at(head, size)) * 1000000000 <= 18446744073709551615 by { solve(); }
                                have to_integer(size) * 1000000000000 <= 18446744073709551615 by { arithmetic() using {
                                    to_integer(at(head, size) / (uint64)1000u32) * 1000 <= to_integer(at(head, size));
                                    to_integer(at(head, size)) * 1000000000 <= 18446744073709551615;
                                }; }
                                assumption();
                            }
                            have i == at(loop(2).entry, i) + 5 implies to_integer(size) * 1000000000000000 <= 18446744073709551615 by {
                                intro();
                                have at(head, i) == at(loop(2).entry, i) + 4 by { auto(); }
                                have to_integer(at(head, size)) * 1000000000000 <= 18446744073709551615 by { solve(); }
                                have to_integer(size) * 1000000000000000 <= 18446744073709551615 by { arithmetic() using {
                                    to_integer(at(head, size) / (uint64)1000u32) * 1000 <= to_integer(at(head, size));
                                    to_integer(at(head, size)) * 1000000000000 <= 18446744073709551615;
                                }; }
                                assumption();
                            }
                            have i == at(loop(2).entry, i) + 6 implies to_integer(size) * 1000000000000000000 <= 18446744073709551615 by {
                                intro();
                                have at(head, i) == at(loop(2).entry, i) + 5 by { auto(); }
                                have to_integer(at(head, size)) * 1000000000000000 <= 18446744073709551615 by { solve(); }
                                have to_integer(size) * 1000000000000000000 <= 18446744073709551615 by { arithmetic() using {
                                    to_integer(at(head, size) / (uint64)1000u32) * 1000 <= to_integer(at(head, size));
                                    to_integer(at(head, size)) * 1000000000000000 <= 18446744073709551615;
                                }; }
                                assumption();
                            }
                            close_invariants() by { solve(); }
                        } else {
                            step();
                            step();
                            step();
                        }
                    }
                }
            }
            have size < 1024u64 by { auto(); }
// The digits of precision: `j` is 0, 1, or 2, and `sf_cap` stays below 1024.
            execute_until(loop(3));
            loop {
                decreases 2 - j;
                invariant 0 <= j and j <= 2;
                invariant 1u32 <= sf_cap and sf_cap <= 1023u32;
                invariant j == 1 implies 10u32 <= sf_cap;
                invariant j == 2 implies 100u32 <= sf_cap;
                initialize by { auto(); }
                preserve by {
                    mark head;
                    execute_until(back_edge());
                    have to_integer(at(head, sf_cap)) * 10 <= 4294967295 by { auto(); }
                    apply(integer::uint32_multiply_guard_by_integer_bound(at(head, sf_cap), 10u32));
                    apply(integer::uint32_multiply_to_integer(at(head, sf_cap), 10u32));
                    have at(head, sf_cap) <= 99u32 by { auto(); }
                    have 1u32 <= sf_cap by { auto(); }
                    have sf_cap <= 1023u32 by { auto(); }
                    have 10u32 <= sf_cap by { auto(); }
                    have at(head, j) < 2 by {
                        if at(head, j) < 2 {
                            assumption();
                        } else {
                            have at(head, j) == 2 by { auto(); }
                            have 100u32 <= at(head, sf_cap) by { solve(); }
                            have 99u32 < at(head, sf_cap) by { auto(); }
                            contradiction(at(head, sf_cap) <= 99u32);
                        }
                    }
                    have j <= 2 by { auto(); }
                    have 0 <= 2 - j by { auto(); }
                    have j == 2 implies 100u32 <= sf_cap by {
                        intro();
                        have at(head, j) == 1 by { auto(); }
                        have 10u32 <= at(head, sf_cap) by { solve(); }
                        have 100u32 <= sf_cap by { auto(); }
                        assumption();
                    }
                    close_invariants() by { solve(); }
                }
            }
// Binary units express the remainder in thousandths.
            branch ensuring {
                fact remainder <= 999u32;
            } then {
                have to_integer(remainder) * 1000 <= 4294967295 by { auto(); }
                apply(integer::uint32_multiply_guard_by_integer_bound(remainder, 1000u32));
                apply(integer::uint32_multiply_to_integer(remainder, 1000u32));
                have remainder * 1000u32 <= 1023000u32 by { auto(); }
                have remainder * 1000u32 >> 10 <= 999u32 by { solve(); }
                step();
                step();
            } else {
                have remainder <= 999u32 by { auto(); }
            }
// Rounding: `rounding[j]` is read through a join on `j`.
            if j == 0 ensuring {
                fact remainder <= 1499u32;
            } then {
                step();
                step();
                have remainder <= 1499u32 by { auto(); }
            } else {
                if j == 1 ensuring {
                    fact remainder <= 1499u32;
                } then {
                    step();
                    step();
                    have remainder <= 1499u32 by { auto(); }
                } else {
                    have 0 <= j and j <= 2 by { auto(); }
                    have 1 <= j by { arithmetic() using { 0 <= j; j != 0; }; }
                    have 2 <= j by { arithmetic() using { 1 <= j; j != 1; }; }
                    have j == 2 by { arithmetic() using { 2 <= j; j <= 2; }; }
                    step();
                    step();
                    have remainder <= 1499u32 by { auto(); }
                }
            }
// The carry keeps `remainder` a three-digit fraction and `size <= 1024`.
            branch ensuring {
                fact remainder <= 999u32;
                fact 1u64 <= size;
                fact size <= 1024u64;
            } then {
                step();
                step();
                have remainder <= 999u32 by { auto(); }
                have 1u64 <= size by { auto(); }
                have size <= 1024u64 by { auto(); }
            } else {
                have remainder <= 999u32 by { auto(); }
                have size <= 1024u64 by { auto(); }
            }
            have 0 <= j and j <= 2 by { auto(); }
// The fraction string: `tmp` is a C string of length `tmp_len(j)` after
// the `if (j)` block, exported through its join. Its length bound comes first,
// so the quantified facts about `tmp` are also read natively.
            if j == 0 ensuring {
                fact tmp_len(j) <= 3u64;
            } then {
                have tmp_len(j) == 0u64 by { unfold(tmp_len(j)); solve(); }
                have tmp_len(j) <= 3u64 by { auto(); }
            } else {
                if j == 1 ensuring {
                    fact tmp_len(j) <= 3u64;
                } then {
                    have tmp_len(j) == 2u64 by { unfold(tmp_len(j)); solve(); }
                    have tmp_len(j) <= 3u64 by { auto(); }
                } else {
                    have 1 <= j by { arithmetic() using { 0 <= j; j != 0; }; }
                    have 2 <= j by { arithmetic() using { 1 <= j; j != 1; }; }
                    have j == 2 by { arithmetic() using { 2 <= j; j <= 2; }; }
                    have tmp_len(j) == 3u64 by { unfold(tmp_len(j)); solve(); }
                    have tmp_len(j) <= 3u64 by { auto(); }
                }
            }
            have to_integer(tmp_len(j)) + 1 <= 18446744073709551615 by { auto(); }
            branch ensuring {
                fact forall (k: uint64) { 0u64 <= k and k < tmp_len(j) implies tmp[k] != 0u8 };
                fact forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) };
                fact tmp[tmp_len(j)] == 0u8;
            } then {
                have 3u64 <= format::padded_length((uint64) remainder, 3u64) by {
                    unfold(format::padded_length((uint64) remainder, 3u64));
                    if format::decimal_length((uint64) remainder) < 3u64 {
                        normalize() using { format::decimal_length((uint64) remainder) < 3u64; };
                    } else {
                        have 3u64 <= format::decimal_length((uint64) remainder) by { auto(); }
                        normalize() using { 3u64 <= format::decimal_length((uint64) remainder); };
                    }
                }
                step();
                have tmp[0u64] == 46u8 by { auto(); }
                have tmp[0u64] != 0u8 by { auto(); }
                have defined(tmp[0u64]) by { solve(); }
                have 0u64 < format::padded_length((uint64) remainder, 3u64) by { auto(); }
                have 1u64 + 0u64 + 1u64 < 12u64 by { normalize(); }
                have tmp[1] == format::padded_digit((uint64) remainder, 3u64, 48u8, 0u64) by {
                    instantiate(forall (k: uint64) { k < format::padded_length((uint64) remainder, 3u64) and 1u64 + k + 1u64 < 12u64 implies tmp[1u64 + k] == format::padded_digit((uint64) remainder, 3u64, 48u8, k) }, 0u64);
                    assumption();
                }
                apply(format::padded_digit_lower_bound((uint64) remainder, 3u64, 0u64));
                have 48u8 <= tmp[1u64] by { auto(); }
                have tmp[1u64] != 0u8 by { auto(); }
                have defined(tmp[1]) by {
                    instantiate(forall (k: uint64) { k < format::padded_length((uint64) remainder, 3u64) and 1u64 + k + 1u64 < 12u64 implies defined(tmp[1u64 + k]) }, 0u64);
                    assumption();
                }
                have 1u64 < format::padded_length((uint64) remainder, 3u64) by { auto(); }
                have 1u64 + 1u64 + 1u64 < 12u64 by { normalize(); }
                have tmp[2] == format::padded_digit((uint64) remainder, 3u64, 48u8, 1u64) by {
                    instantiate(forall (k: uint64) { k < format::padded_length((uint64) remainder, 3u64) and 1u64 + k + 1u64 < 12u64 implies tmp[1u64 + k] == format::padded_digit((uint64) remainder, 3u64, 48u8, k) }, 1u64);
                    assumption();
                }
                apply(format::padded_digit_lower_bound((uint64) remainder, 3u64, 1u64));
                have 48u8 <= tmp[2u64] by { auto(); }
                have tmp[2u64] != 0u8 by { auto(); }
                have defined(tmp[2]) by {
                    instantiate(forall (k: uint64) { k < format::padded_length((uint64) remainder, 3u64) and 1u64 + k + 1u64 < 12u64 implies defined(tmp[1u64 + k]) }, 1u64);
                    assumption();
                }
                if j == 1 ensuring {
                    fact to_integer(tmp_len(j)) + 1 <= 18446744073709551615;
                    fact forall (k: uint64) { 0u64 <= k and k < tmp_len(j) implies tmp[k] != 0u8 };
                    fact forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) };
                    fact tmp[tmp_len(j)] == 0u8;
                } then {
                    mark fmt;
                    step();
                    transport(at(fmt, tmp[0u64]) != 0u8, tmp[0u64] != 0u8);
                    transport(defined(at(fmt, tmp[0u64])), defined(tmp[0u64])) using { defined(at(fmt, tmp[0u64])); j == 1; }
                    transport(at(fmt, tmp[1u64]) != 0u8, tmp[1u64] != 0u8);
                    transport(defined(at(fmt, tmp[1u64])), defined(tmp[1u64])) using { defined(at(fmt, tmp[1u64])); j == 1; }
                    have defined(tmp[2u64]) by { normalize() using { j == 1; }; }
                    have tmp[2u64] == 0u8 by { normalize() using { j == 1; }; }
                    have tmp_len(j) == 2u64 by { unfold(tmp_len(j)); solve(); }
                    have to_integer(tmp_len(j)) + 1 <= 18446744073709551615 by { auto(); }
                    have forall (k: uint64) { 0u64 <= k and k < 2u64 implies tmp[k] != 0u8 } by { enumerate(); }
                    have forall (k: uint64) { 0u64 <= k and k < 3u64 implies defined(tmp[k]) } by { enumerate(); }
                    have forall (k: uint64) { 0u64 <= k and k < tmp_len(j) implies tmp[k] != 0u8 } by {
                        intro();
                        intro();
                        have k < 2u64 by { arithmetic() using { k < tmp_len(j); tmp_len(j) == 2u64; }; }
                        instantiate(forall (k: uint64) { 0u64 <= k and k < 2u64 implies tmp[k] != 0u8 }, k);
                        assumption();
                    }
                    have forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) } by {
                        intro();
                        intro();
                        have k < 3u64 by { arithmetic() using { k < tmp_len(j) + 1u64; tmp_len(j) == 2u64; }; }
                        instantiate(forall (k: uint64) { 0u64 <= k and k < 3u64 implies defined(tmp[k]) }, k);
                        assumption();
                    }
                } else {
                    have 0 <= j and j <= 2 by { auto(); }
                    have 1 <= j by { arithmetic() using { 0 <= j; j != 0; }; }
                    have 2 <= j by { arithmetic() using { 1 <= j; j != 1; }; }
                    have j == 2 by { arithmetic() using { 2 <= j; j <= 2; }; }
                    mark fmt;
                    step();
                    transport(at(fmt, tmp[0u64]) != 0u8, tmp[0u64] != 0u8);
                    transport(defined(at(fmt, tmp[0u64])), defined(tmp[0u64])) using { defined(at(fmt, tmp[0u64])); j == 2; }
                    transport(at(fmt, tmp[1u64]) != 0u8, tmp[1u64] != 0u8);
                    transport(defined(at(fmt, tmp[1u64])), defined(tmp[1u64])) using { defined(at(fmt, tmp[1u64])); j == 2; }
                    transport(at(fmt, tmp[2u64]) != 0u8, tmp[2u64] != 0u8);
                    transport(defined(at(fmt, tmp[2u64])), defined(tmp[2u64])) using { defined(at(fmt, tmp[2u64])); j == 2; }
                    have defined(tmp[3u64]) by { normalize() using { j == 2; }; }
                    have tmp[3u64] == 0u8 by { normalize() using { j == 2; }; }
                    have tmp_len(j) == 3u64 by { unfold(tmp_len(j)); solve(); }
                    have to_integer(tmp_len(j)) + 1 <= 18446744073709551615 by { auto(); }
                    have forall (k: uint64) { 0u64 <= k and k < 3u64 implies tmp[k] != 0u8 } by { enumerate(); }
                    have forall (k: uint64) { 0u64 <= k and k < 4u64 implies defined(tmp[k]) } by { enumerate(); }
                    have forall (k: uint64) { 0u64 <= k and k < tmp_len(j) implies tmp[k] != 0u8 } by {
                        intro();
                        intro();
                        have k < 3u64 by { arithmetic() using { k < tmp_len(j); tmp_len(j) == 3u64; }; }
                        instantiate(forall (k: uint64) { 0u64 <= k and k < 3u64 implies tmp[k] != 0u8 }, k);
                        assumption();
                    }
                    have forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) } by {
                        intro();
                        intro();
                        have k < 4u64 by { arithmetic() using { k < tmp_len(j) + 1u64; tmp_len(j) == 3u64; }; }
                        instantiate(forall (k: uint64) { 0u64 <= k and k < 4u64 implies defined(tmp[k]) }, k);
                        assumption();
                    }
                }
            } else {
                have j == 0 by { auto(); }
                have tmp_len(j) == 0u64 by { unfold(tmp_len(j)); solve(); }
                have to_integer(tmp_len(j)) + 1 <= 18446744073709551615 by { auto(); }
                have forall (k: uint64) { 0u64 <= k and k < tmp_len(j) implies tmp[k] != 0u8 } by {
                    intro();
                    intro();
                    have false by { arithmetic() using { k < tmp_len(j); tmp_len(j) == 0u64; }; }
                    contradiction(false);
                }
                have forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) } by {
                    intro();
                    intro();
                    have k < 1u64 by { arithmetic() using { k < tmp_len(j) + 1u64; tmp_len(j) == 0u64; }; }
                    have k == 0u64 by { arithmetic() using { k < 1u64; }; }
                    rewrite(k == 0u64);
                    solve();
                }
            }
// The unit and the final call: one case per unit string, each split by the
// two flags into the four literal combinations the call prints.
            mark tmp_ready;
            have format::decimal_length((uint64)(uint32) size) <= 20u64 by {
                unfold(format::decimal_length((uint64)(uint32) size));
                have format::decimal_length((uint64)(uint32) size) <= 20u64 by { auto(); }
                assumption();
            }
            have (uint64) len != 0u64 by { auto(); }
            if 9 <= i {
                step();
                step();
                transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                if (units & 1073741824u32) != 0u32 {
                    if (units & 2147483648u32) != 0u32 {
                        step(snprintf, { n1: tmp_len(j) });
                        execute();
                        solve();
                    } else {
                        step(snprintf, { n1: tmp_len(j) });
                        execute();
                        solve();
                    }
                } else {
                    if (units & 2147483648u32) != 0u32 {
                        step(snprintf, { n1: tmp_len(j) });
                        execute();
                        solve();
                    } else {
                        step(snprintf, { n1: tmp_len(j) });
                        execute();
                        solve();
                    }
                }
            } else {
                step();
                have 0 <= i by { auto(); }
                have i <= 8 by { arithmetic() using { not (9 <= i); }; }
                if (units & 1u32) == 1u32 {
                    if i == 0 {
                        step();
                        step();
                        transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                        if (units & 1073741824u32) != 0u32 {
                            if (units & 2147483648u32) != 0u32 {
                                step(snprintf, { n1: tmp_len(j) });
                                execute();
                                solve();
                            } else {
                                step(snprintf, { n1: tmp_len(j) });
                                execute();
                                solve();
                            }
                        } else {
                            if (units & 2147483648u32) != 0u32 {
                                step(snprintf, { n1: tmp_len(j) });
                                execute();
                                solve();
                            } else {
                                step(snprintf, { n1: tmp_len(j) });
                                execute();
                                solve();
                            }
                        }
                    } else {
                        have 1 <= i by { arithmetic() using { 0 <= i; i != 0; }; }
                        if i == 1 {
                            step();
                            step();
                            transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                            if (units & 1073741824u32) != 0u32 {
                                if (units & 2147483648u32) != 0u32 {
                                    step(snprintf, { n1: tmp_len(j) });
                                    execute();
                                    solve();
                                } else {
                                    step(snprintf, { n1: tmp_len(j) });
                                    execute();
                                    solve();
                                }
                            } else {
                                if (units & 2147483648u32) != 0u32 {
                                    step(snprintf, { n1: tmp_len(j) });
                                    execute();
                                    solve();
                                } else {
                                    step(snprintf, { n1: tmp_len(j) });
                                    execute();
                                    solve();
                                }
                            }
                        } else {
                            have 2 <= i by { arithmetic() using { 1 <= i; i != 1; }; }
                            if i == 2 {
                                step();
                                step();
                                transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                                if (units & 1073741824u32) != 0u32 {
                                    if (units & 2147483648u32) != 0u32 {
                                        step(snprintf, { n1: tmp_len(j) });
                                        execute();
                                        solve();
                                    } else {
                                        step(snprintf, { n1: tmp_len(j) });
                                        execute();
                                        solve();
                                    }
                                } else {
                                    if (units & 2147483648u32) != 0u32 {
                                        step(snprintf, { n1: tmp_len(j) });
                                        execute();
                                        solve();
                                    } else {
                                        step(snprintf, { n1: tmp_len(j) });
                                        execute();
                                        solve();
                                    }
                                }
                            } else {
                                have 3 <= i by { arithmetic() using { 2 <= i; i != 2; }; }
                                if i == 3 {
                                    step();
                                    step();
                                    transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                                    if (units & 1073741824u32) != 0u32 {
                                        if (units & 2147483648u32) != 0u32 {
                                            step(snprintf, { n1: tmp_len(j) });
                                            execute();
                                            solve();
                                        } else {
                                            step(snprintf, { n1: tmp_len(j) });
                                            execute();
                                            solve();
                                        }
                                    } else {
                                        if (units & 2147483648u32) != 0u32 {
                                            step(snprintf, { n1: tmp_len(j) });
                                            execute();
                                            solve();
                                        } else {
                                            step(snprintf, { n1: tmp_len(j) });
                                            execute();
                                            solve();
                                        }
                                    }
                                } else {
                                    have 4 <= i by { arithmetic() using { 3 <= i; i != 3; }; }
                                    if i == 4 {
                                        step();
                                        step();
                                        transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                                        if (units & 1073741824u32) != 0u32 {
                                            if (units & 2147483648u32) != 0u32 {
                                                step(snprintf, { n1: tmp_len(j) });
                                                execute();
                                                solve();
                                            } else {
                                                step(snprintf, { n1: tmp_len(j) });
                                                execute();
                                                solve();
                                            }
                                        } else {
                                            if (units & 2147483648u32) != 0u32 {
                                                step(snprintf, { n1: tmp_len(j) });
                                                execute();
                                                solve();
                                            } else {
                                                step(snprintf, { n1: tmp_len(j) });
                                                execute();
                                                solve();
                                            }
                                        }
                                    } else {
                                        have 5 <= i by { arithmetic() using { 4 <= i; i != 4; }; }
                                        if i == 5 {
                                            step();
                                            step();
                                            transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                                            if (units & 1073741824u32) != 0u32 {
                                                if (units & 2147483648u32) != 0u32 {
                                                    step(snprintf, { n1: tmp_len(j) });
                                                    execute();
                                                    solve();
                                                } else {
                                                    step(snprintf, { n1: tmp_len(j) });
                                                    execute();
                                                    solve();
                                                }
                                            } else {
                                                if (units & 2147483648u32) != 0u32 {
                                                    step(snprintf, { n1: tmp_len(j) });
                                                    execute();
                                                    solve();
                                                } else {
                                                    step(snprintf, { n1: tmp_len(j) });
                                                    execute();
                                                    solve();
                                                }
                                            }
                                        } else {
                                            have 6 <= i by { arithmetic() using { 5 <= i; i != 5; }; }
                                            if i == 6 {
                                                step();
                                                step();
                                                transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                                                if (units & 1073741824u32) != 0u32 {
                                                    if (units & 2147483648u32) != 0u32 {
                                                        step(snprintf, { n1: tmp_len(j) });
                                                        execute();
                                                        solve();
                                                    } else {
                                                        step(snprintf, { n1: tmp_len(j) });
                                                        execute();
                                                        solve();
                                                    }
                                                } else {
                                                    if (units & 2147483648u32) != 0u32 {
                                                        step(snprintf, { n1: tmp_len(j) });
                                                        execute();
                                                        solve();
                                                    } else {
                                                        step(snprintf, { n1: tmp_len(j) });
                                                        execute();
                                                        solve();
                                                    }
                                                }
                                            } else {
                                                have 7 <= i by { arithmetic() using { 6 <= i; i != 6; }; }
                                                if i == 7 {
                                                    step();
                                                    step();
                                                    transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                                                    if (units & 1073741824u32) != 0u32 {
                                                        if (units & 2147483648u32) != 0u32 {
                                                            step(snprintf, { n1: tmp_len(j) });
                                                            execute();
                                                            solve();
                                                        } else {
                                                            step(snprintf, { n1: tmp_len(j) });
                                                            execute();
                                                            solve();
                                                        }
                                                    } else {
                                                        if (units & 2147483648u32) != 0u32 {
                                                            step(snprintf, { n1: tmp_len(j) });
                                                            execute();
                                                            solve();
                                                        } else {
                                                            step(snprintf, { n1: tmp_len(j) });
                                                            execute();
                                                            solve();
                                                        }
                                                    }
                                                } else {
                                                    have 8 <= i by { arithmetic() using { 7 <= i; i != 7; }; }
                                                    have i == 8 by { arithmetic() using { 8 <= i; i <= 8; }; }
                                                    step();
                                                    step();
                                                    transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                                                    if (units & 1073741824u32) != 0u32 {
                                                        if (units & 2147483648u32) != 0u32 {
                                                            step(snprintf, { n1: tmp_len(j) });
                                                            execute();
                                                            solve();
                                                        } else {
                                                            step(snprintf, { n1: tmp_len(j) });
                                                            execute();
                                                            solve();
                                                        }
                                                    } else {
                                                        if (units & 2147483648u32) != 0u32 {
                                                            step(snprintf, { n1: tmp_len(j) });
                                                            execute();
                                                            solve();
                                                        } else {
                                                            step(snprintf, { n1: tmp_len(j) });
                                                            execute();
                                                            solve();
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
                } else {
                    if i == 0 {
                        step();
                        step();
                        transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                        if (units & 1073741824u32) != 0u32 {
                            if (units & 2147483648u32) != 0u32 {
                                step(snprintf, { n1: tmp_len(j) });
                                execute();
                                solve();
                            } else {
                                step(snprintf, { n1: tmp_len(j) });
                                execute();
                                solve();
                            }
                        } else {
                            if (units & 2147483648u32) != 0u32 {
                                step(snprintf, { n1: tmp_len(j) });
                                execute();
                                solve();
                            } else {
                                step(snprintf, { n1: tmp_len(j) });
                                execute();
                                solve();
                            }
                        }
                    } else {
                        have 1 <= i by { arithmetic() using { 0 <= i; i != 0; }; }
                        if i == 1 {
                            step();
                            step();
                            transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                            if (units & 1073741824u32) != 0u32 {
                                if (units & 2147483648u32) != 0u32 {
                                    step(snprintf, { n1: tmp_len(j) });
                                    execute();
                                    solve();
                                } else {
                                    step(snprintf, { n1: tmp_len(j) });
                                    execute();
                                    solve();
                                }
                            } else {
                                if (units & 2147483648u32) != 0u32 {
                                    step(snprintf, { n1: tmp_len(j) });
                                    execute();
                                    solve();
                                } else {
                                    step(snprintf, { n1: tmp_len(j) });
                                    execute();
                                    solve();
                                }
                            }
                        } else {
                            have 2 <= i by { arithmetic() using { 1 <= i; i != 1; }; }
                            if i == 2 {
                                step();
                                step();
                                transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                                if (units & 1073741824u32) != 0u32 {
                                    if (units & 2147483648u32) != 0u32 {
                                        step(snprintf, { n1: tmp_len(j) });
                                        execute();
                                        solve();
                                    } else {
                                        step(snprintf, { n1: tmp_len(j) });
                                        execute();
                                        solve();
                                    }
                                } else {
                                    if (units & 2147483648u32) != 0u32 {
                                        step(snprintf, { n1: tmp_len(j) });
                                        execute();
                                        solve();
                                    } else {
                                        step(snprintf, { n1: tmp_len(j) });
                                        execute();
                                        solve();
                                    }
                                }
                            } else {
                                have 3 <= i by { arithmetic() using { 2 <= i; i != 2; }; }
                                if i == 3 {
                                    step();
                                    step();
                                    transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                                    if (units & 1073741824u32) != 0u32 {
                                        if (units & 2147483648u32) != 0u32 {
                                            step(snprintf, { n1: tmp_len(j) });
                                            execute();
                                            solve();
                                        } else {
                                            step(snprintf, { n1: tmp_len(j) });
                                            execute();
                                            solve();
                                        }
                                    } else {
                                        if (units & 2147483648u32) != 0u32 {
                                            step(snprintf, { n1: tmp_len(j) });
                                            execute();
                                            solve();
                                        } else {
                                            step(snprintf, { n1: tmp_len(j) });
                                            execute();
                                            solve();
                                        }
                                    }
                                } else {
                                    have 4 <= i by { arithmetic() using { 3 <= i; i != 3; }; }
                                    if i == 4 {
                                        step();
                                        step();
                                        transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                                        if (units & 1073741824u32) != 0u32 {
                                            if (units & 2147483648u32) != 0u32 {
                                                step(snprintf, { n1: tmp_len(j) });
                                                execute();
                                                solve();
                                            } else {
                                                step(snprintf, { n1: tmp_len(j) });
                                                execute();
                                                solve();
                                            }
                                        } else {
                                            if (units & 2147483648u32) != 0u32 {
                                                step(snprintf, { n1: tmp_len(j) });
                                                execute();
                                                solve();
                                            } else {
                                                step(snprintf, { n1: tmp_len(j) });
                                                execute();
                                                solve();
                                            }
                                        }
                                    } else {
                                        have 5 <= i by { arithmetic() using { 4 <= i; i != 4; }; }
                                        if i == 5 {
                                            step();
                                            step();
                                            transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                                            if (units & 1073741824u32) != 0u32 {
                                                if (units & 2147483648u32) != 0u32 {
                                                    step(snprintf, { n1: tmp_len(j) });
                                                    execute();
                                                    solve();
                                                } else {
                                                    step(snprintf, { n1: tmp_len(j) });
                                                    execute();
                                                    solve();
                                                }
                                            } else {
                                                if (units & 2147483648u32) != 0u32 {
                                                    step(snprintf, { n1: tmp_len(j) });
                                                    execute();
                                                    solve();
                                                } else {
                                                    step(snprintf, { n1: tmp_len(j) });
                                                    execute();
                                                    solve();
                                                }
                                            }
                                        } else {
                                            have 6 <= i by { arithmetic() using { 5 <= i; i != 5; }; }
                                            if i == 6 {
                                                step();
                                                step();
                                                transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                                                if (units & 1073741824u32) != 0u32 {
                                                    if (units & 2147483648u32) != 0u32 {
                                                        step(snprintf, { n1: tmp_len(j) });
                                                        execute();
                                                        solve();
                                                    } else {
                                                        step(snprintf, { n1: tmp_len(j) });
                                                        execute();
                                                        solve();
                                                    }
                                                } else {
                                                    if (units & 2147483648u32) != 0u32 {
                                                        step(snprintf, { n1: tmp_len(j) });
                                                        execute();
                                                        solve();
                                                    } else {
                                                        step(snprintf, { n1: tmp_len(j) });
                                                        execute();
                                                        solve();
                                                    }
                                                }
                                            } else {
                                                have 7 <= i by { arithmetic() using { 6 <= i; i != 6; }; }
                                                if i == 7 {
                                                    step();
                                                    step();
                                                    transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                                                    if (units & 1073741824u32) != 0u32 {
                                                        if (units & 2147483648u32) != 0u32 {
                                                            step(snprintf, { n1: tmp_len(j) });
                                                            execute();
                                                            solve();
                                                        } else {
                                                            step(snprintf, { n1: tmp_len(j) });
                                                            execute();
                                                            solve();
                                                        }
                                                    } else {
                                                        if (units & 2147483648u32) != 0u32 {
                                                            step(snprintf, { n1: tmp_len(j) });
                                                            execute();
                                                            solve();
                                                        } else {
                                                            step(snprintf, { n1: tmp_len(j) });
                                                            execute();
                                                            solve();
                                                        }
                                                    }
                                                } else {
                                                    have 8 <= i by { arithmetic() using { 7 <= i; i != 7; }; }
                                                    have i == 8 by { arithmetic() using { 8 <= i; i <= 8; }; }
                                                    step();
                                                    step();
                                                    transport(forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(at(tmp_ready, tmp[k])) }, forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) });
                                                    if (units & 1073741824u32) != 0u32 {
                                                        if (units & 2147483648u32) != 0u32 {
                                                            step(snprintf, { n1: tmp_len(j) });
                                                            execute();
                                                            solve();
                                                        } else {
                                                            step(snprintf, { n1: tmp_len(j) });
                                                            execute();
                                                            solve();
                                                        }
                                                    } else {
                                                        if (units & 2147483648u32) != 0u32 {
                                                            step(snprintf, { n1: tmp_len(j) });
                                                            execute();
                                                            solve();
                                                        } else {
                                                            step(snprintf, { n1: tmp_len(j) });
                                                            execute();
                                                            solve();
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
            }
        }
    }
}
