verifying "round.cpp";
int64 rounded(int128 n, int32 d, bool round_down) {
    requires -9223372036854775808 * to_integer(d) <= to_integer(n);
    requires to_integer(n) <= 9223372036854775807 * to_integer(d);
    requires d > 0;
    requires d <= 100;
    ensures -9223372036854775808 <= to_integer(result);
    ensures to_integer(result) <= 9223372036854775807;
    ensures -9223372036854775808i64 <= result;
    ensures result <= 9223372036854775807i64;
    ensures round_down != 0 and truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1;
    ensures round_down != 0 and 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d));
    ensures round_down == 0 and 0 < truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1;
    ensures round_down == 0 and truncating_remainder(to_integer(n), to_integer(d)) <= 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d));
    ensures round_down != 0 implies to_integer(result) * to_integer(d) <= to_integer(n);
    ensures round_down != 0 implies to_integer(n) < (to_integer(result) + 1) * to_integer(d);
    ensures round_down == 0 implies to_integer(n) <= to_integer(result) * to_integer(d);
    ensures round_down == 0 implies (to_integer(result) + -1) * to_integer(d) < to_integer(n);
} by {
    have 1 <= d by { arithmetic() using { d > 0; } }
    apply(int32_less_equal_to_integer(1, d));
    apply(int32_less_equal_to_integer(d, 100));
    have -922337203685477580800 <= to_integer(n) by { arithmetic() using {
        -9223372036854775808 * to_integer(d) <= to_integer(n);
        to_integer(d) <= 100;
    } }
    have to_integer(n) <= 922337203685477580700 by { arithmetic() using {
        to_integer(n) <= 9223372036854775807 * to_integer(d);
        to_integer(d) <= 100;
    } }
    have to_integer(d) != 0 by { arithmetic_certificate special {
        premise 0: 1 <= to_integer(d) => 1 <= to_integer(d);
        integer_bound_exclusion bounds [0] => to_integer(d) != 0; conclusion 0;
    } }
    have to_integer(d) != -1 by { arithmetic_certificate special {
        premise 0: 1 <= to_integer(d) => 1 <= to_integer(d);
        integer_bound_exclusion bounds [0] => to_integer(d) != -1; conclusion 0;
    } }
    step();
    have -9223372036854775808 <= truncating_quotient(to_integer(n), to_integer(d)) by {
        apply(integer_positive_divisor_quotient_lower(to_integer(n), to_integer(d), -9223372036854775808));
    }
    have truncating_quotient(to_integer(n), to_integer(d)) <= 9223372036854775807 by {
        apply(integer_positive_divisor_quotient_upper(to_integer(n), to_integer(d), 9223372036854775807));
    }
    have -9223372036854775808 <= to_integer(n / (int128)d) by { arithmetic_certificate special {
        premise 0: to_integer(n / (int128)d) == truncating_quotient(to_integer(n), to_integer(d)) => to_integer(n / (int128)d) == truncating_quotient(to_integer(n), to_integer(d));
        premise 1: -9223372036854775808 <= truncating_quotient(to_integer(n), to_integer(d)) => -9223372036854775808 <= truncating_quotient(to_integer(n), to_integer(d));
        integer_relation_transport bounds [0, 1] => -9223372036854775808 <= to_integer(n / (int128)d); conclusion 0;
    } }
    have to_integer(n / (int128)d) <= 9223372036854775807 by { arithmetic_certificate special {
        premise 0: to_integer(n / (int128)d) == truncating_quotient(to_integer(n), to_integer(d)) => to_integer(n / (int128)d) == truncating_quotient(to_integer(n), to_integer(d));
        premise 1: truncating_quotient(to_integer(n), to_integer(d)) <= 9223372036854775807 => truncating_quotient(to_integer(n), to_integer(d)) <= 9223372036854775807;
        integer_relation_transport bounds [0, 1] => to_integer(n / (int128)d) <= 9223372036854775807; conclusion 0;
    } }
    have to_integer(quot) == to_integer(n / (int128)d) by { arithmetic_certificate special {
        premise 0: -9223372036854775808 <= to_integer(n / (int128)d) => -9223372036854775808 <= to_integer(n / (int128)d);
        premise 1: to_integer(n / (int128)d) <= 9223372036854775807 => to_integer(n / (int128)d) <= 9223372036854775807;
        integer_cast_identity bounds [0, 1] => to_integer(quot) == to_integer(n / (int128)d); conclusion 0;
    } }
    have -9223372036854775808 <= to_integer(quot) by { arithmetic_certificate special {
        premise 0: to_integer(quot) == to_integer(n / (int128)d) => to_integer(quot) == to_integer(n / (int128)d);
        premise 1: -9223372036854775808 <= to_integer(n / (int128)d) => -9223372036854775808 <= to_integer(n / (int128)d);
        integer_relation_transport bounds [0, 1] => -9223372036854775808 <= to_integer(quot); conclusion 0;
    } }
    have to_integer(quot) <= 9223372036854775807 by { arithmetic_certificate special {
        premise 0: to_integer(quot) == to_integer(n / (int128)d) => to_integer(quot) == to_integer(n / (int128)d);
        premise 1: to_integer(n / (int128)d) <= 9223372036854775807 => to_integer(n / (int128)d) <= 9223372036854775807;
        integer_relation_transport bounds [0, 1] => to_integer(quot) <= 9223372036854775807; conclusion 0;
    } }
    apply(int64_less_equal_of_to_integer(-9223372036854775808i64, quot));
    apply(int64_less_equal_of_to_integer(quot, 9223372036854775807i64));
    step();
    have -99 <= truncating_remainder(to_integer(n), to_integer(d)) by { arithmetic_certificate special {
        premise 0: -922337203685477580800 <= to_integer(n) => -922337203685477580800 <= to_integer(n);
        premise 1: to_integer(n) <= 922337203685477580700 => to_integer(n) <= 922337203685477580700;
        premise 2: 1 <= to_integer(d) => 1 <= to_integer(d);
        premise 3: to_integer(d) <= 100 => to_integer(d) <= 100;
        integer_division_bounds bounds [0, 1, 2, 3] => -99 <= truncating_remainder(to_integer(n), to_integer(d)); conclusion 0;
    } }
    have truncating_remainder(to_integer(n), to_integer(d)) <= 99 by { arithmetic_certificate special {
        premise 0: -922337203685477580800 <= to_integer(n) => -922337203685477580800 <= to_integer(n);
        premise 1: to_integer(n) <= 922337203685477580700 => to_integer(n) <= 922337203685477580700;
        premise 2: 1 <= to_integer(d) => 1 <= to_integer(d);
        premise 3: to_integer(d) <= 100 => to_integer(d) <= 100;
        integer_division_bounds bounds [0, 1, 2, 3] => truncating_remainder(to_integer(n), to_integer(d)) <= 99; conclusion 0;
    } }
    have -99 <= to_integer(n % (int128)d) by { arithmetic_certificate special {
        premise 0: to_integer(n % (int128)d) == truncating_remainder(to_integer(n), to_integer(d)) => to_integer(n % (int128)d) == truncating_remainder(to_integer(n), to_integer(d));
        premise 1: -99 <= truncating_remainder(to_integer(n), to_integer(d)) => -99 <= truncating_remainder(to_integer(n), to_integer(d));
        integer_relation_transport bounds [0, 1] => -99 <= to_integer(n % (int128)d); conclusion 0;
    } }
    have to_integer(n % (int128)d) <= 99 by { arithmetic_certificate special {
        premise 0: to_integer(n % (int128)d) == truncating_remainder(to_integer(n), to_integer(d)) => to_integer(n % (int128)d) == truncating_remainder(to_integer(n), to_integer(d));
        premise 1: truncating_remainder(to_integer(n), to_integer(d)) <= 99 => truncating_remainder(to_integer(n), to_integer(d)) <= 99;
        integer_relation_transport bounds [0, 1] => to_integer(n % (int128)d) <= 99; conclusion 0;
    } }
    have to_integer(mod) == to_integer(n % (int128)d) by { arithmetic_certificate special {
        premise 0: -99 <= to_integer(n % (int128)d) => -99 <= to_integer(n % (int128)d);
        premise 1: to_integer(n % (int128)d) <= 99 => to_integer(n % (int128)d) <= 99;
        integer_cast_identity bounds [0, 1] => to_integer(mod) == to_integer(n % (int128)d); conclusion 0;
    } }
    have -99 <= to_integer(mod) by { arithmetic_certificate special {
        premise 0: to_integer(mod) == to_integer(n % (int128)d) => to_integer(mod) == to_integer(n % (int128)d);
        premise 1: -99 <= to_integer(n % (int128)d) => -99 <= to_integer(n % (int128)d);
        integer_relation_transport bounds [0, 1] => -99 <= to_integer(mod); conclusion 0;
    } }
    have to_integer(mod) <= 99 by { arithmetic_certificate special {
        premise 0: to_integer(mod) == to_integer(n % (int128)d) => to_integer(mod) == to_integer(n % (int128)d);
        premise 1: to_integer(n % (int128)d) <= 99 => to_integer(n % (int128)d) <= 99;
        integer_relation_transport bounds [0, 1] => to_integer(mod) <= 99; conclusion 0;
    } }
    apply(int32_less_equal_of_to_integer(-99, mod));
    apply(int32_less_equal_of_to_integer(mod, 99));
    have 0 < to_integer(d) by { arithmetic() using { 1 <= to_integer(d); } }
    apply(integer_positive_divisor_remainder_lower(to_integer(n), to_integer(d)));
    apply(integer_positive_divisor_remainder_upper(to_integer(n), to_integer(d)));
    apply(integer_truncation_identity(to_integer(n), to_integer(d)));
    have to_integer(quot) == truncating_quotient(to_integer(n), to_integer(d)) by { arithmetic_certificate special {
        premise 0: to_integer(quot) == to_integer(n / (int128)d) => to_integer(quot) == to_integer(n / (int128)d);
        premise 1: to_integer(n / (int128)d) == truncating_quotient(to_integer(n), to_integer(d)) => to_integer(n / (int128)d) == truncating_quotient(to_integer(n), to_integer(d));
        integer_relation_transport bounds [0, 1] => to_integer(quot) == truncating_quotient(to_integer(n), to_integer(d)); conclusion 0;
    } }
    have to_integer(mod) == truncating_remainder(to_integer(n), to_integer(d)) by { arithmetic_certificate special {
        premise 0: to_integer(mod) == to_integer(n % (int128)d) => to_integer(mod) == to_integer(n % (int128)d);
        premise 1: to_integer(n % (int128)d) == truncating_remainder(to_integer(n), to_integer(d)) => to_integer(n % (int128)d) == truncating_remainder(to_integer(n), to_integer(d));
        integer_relation_transport bounds [0, 1] => to_integer(mod) == truncating_remainder(to_integer(n), to_integer(d)); conclusion 0;
    } }
    have to_integer(n) == to_integer(quot) * to_integer(d) + to_integer(mod) by {
        rewrite(to_integer(quot) == truncating_quotient(to_integer(n), to_integer(d)));
        rewrite(to_integer(mod) == truncating_remainder(to_integer(n), to_integer(d)));
        simp();
    }

    have defined(quot + 0i64) by simp;
    apply(int64_add_to_integer(quot, 0i64));
    have -9223372036854775808 <= to_integer(quot + 0i64) by { arithmetic() using {
        to_integer(quot + 0i64) == to_integer(quot) + 0;
        -9223372036854775808 <= to_integer(quot); to_integer(quot) <= 9223372036854775807;
    } }
    have to_integer(quot + 0i64) <= 9223372036854775807 by { arithmetic() using {
        to_integer(quot + 0i64) == to_integer(quot) + 0;
        -9223372036854775808 <= to_integer(quot); to_integer(quot) <= 9223372036854775807;
    } }
    have to_integer(quot + 0i64) == truncating_quotient(to_integer(n), to_integer(d)) by {
        rewrite(to_integer(quot + 0i64) == to_integer(quot) + 0);
        assumption();
    }
    if 0 < mod {
        apply(int32_less_than_to_integer(0, mod));
        apply(integer_upper_correction_bound(to_integer(n), to_integer(d), to_integer(quot), to_integer(mod), 9223372036854775807));
        apply(int64_less_equal_of_to_integer(quot, 9223372036854775806i64));
        have defined(quot + 1i64) by simp;
        apply(int64_add_to_integer(quot, 1i64));
        have -9223372036854775808 <= to_integer(quot + 1i64) by { arithmetic() using {
            to_integer(quot + 1i64) == to_integer(quot) + 1;
            -9223372036854775808 <= to_integer(quot); to_integer(quot) <= 9223372036854775806;
        } }
        have to_integer(quot + 1i64) <= 9223372036854775807 by { arithmetic() using {
            to_integer(quot + 1i64) == to_integer(quot) + 1;
            -9223372036854775808 <= to_integer(quot); to_integer(quot) <= 9223372036854775806;
        } }
        have to_integer(quot + 1i64) == truncating_quotient(to_integer(n), to_integer(d)) + 1 by {
            rewrite(to_integer(quot + 1i64) == to_integer(quot) + 1);
            rewrite(to_integer(quot) == truncating_quotient(to_integer(n), to_integer(d)));
            simp();
        }

        have not (truncating_remainder(to_integer(n), to_integer(d)) < 0) by {
            rewrite(truncating_remainder(to_integer(n), to_integer(d)) == to_integer(mod));
            arithmetic() using { 0 < to_integer(mod); }
        }
        have 0 <= truncating_remainder(to_integer(n), to_integer(d)) by {
            rewrite(truncating_remainder(to_integer(n), to_integer(d)) == to_integer(mod));
            arithmetic() using { 0 < to_integer(mod); }
        }
        have 0 < truncating_remainder(to_integer(n), to_integer(d)) by {
            rewrite(truncating_remainder(to_integer(n), to_integer(d)) == to_integer(mod));
            arithmetic() using { 0 < to_integer(mod); }
        }
        have not (truncating_remainder(to_integer(n), to_integer(d)) <= 0) by {
            rewrite(truncating_remainder(to_integer(n), to_integer(d)) == to_integer(mod));
            arithmetic() using { 0 < to_integer(mod); }
        }
        if round_down == 0 {
            execute();
            have -9223372036854775808 <= to_integer(result) by simp;
            have to_integer(result) <= 9223372036854775807 by simp;
            apply(int64_less_equal_of_to_integer(-9223372036854775808i64, result));
            apply(int64_less_equal_of_to_integer(result, 9223372036854775807i64));
            have to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1 by simp;
            have round_down != 0 and truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1 by {
                intro();
                contradiction(truncating_remainder(to_integer(n), to_integer(d)) < 0);
            }
            have round_down != 0 and 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                intro();
                contradiction(round_down == 0);
            }
            have round_down == 0 and 0 < truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1 by {
                intro();
                assumption();
            }
            have round_down == 0 and truncating_remainder(to_integer(n), to_integer(d)) <= 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                intro();
                contradiction(truncating_remainder(to_integer(n), to_integer(d)) <= 0);
            }
            have 0 < truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1 by {
                intro();
                assumption();
            }
            have truncating_remainder(to_integer(n), to_integer(d)) <= 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                intro();
                contradiction(truncating_remainder(to_integer(n), to_integer(d)) <= 0);
            }
            apply(integer_ceiling_from_remainder(to_integer(n), to_integer(d), truncating_quotient(to_integer(n), to_integer(d)), truncating_remainder(to_integer(n), to_integer(d)), to_integer(result)));
            have round_down != 0 implies to_integer(result) * to_integer(d) <= to_integer(n) by {
                intro();
                contradiction(round_down == 0);
            }
            have round_down != 0 implies to_integer(n) < (to_integer(result) + 1) * to_integer(d) by {
                intro();
                contradiction(round_down == 0);
            }
            have round_down == 0 implies to_integer(n) <= to_integer(result) * to_integer(d) by {
                intro();
                assumption();
            }
            have round_down == 0 implies (to_integer(result) + -1) * to_integer(d) < to_integer(n) by {
                intro();
                assumption();
            }
            simp();
        } else {
            execute();
            have -9223372036854775808 <= to_integer(result) by simp;
            have to_integer(result) <= 9223372036854775807 by simp;
            apply(int64_less_equal_of_to_integer(-9223372036854775808i64, result));
            apply(int64_less_equal_of_to_integer(result, 9223372036854775807i64));
            have to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by simp;
            have round_down != 0 and truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1 by {
                intro();
                contradiction(truncating_remainder(to_integer(n), to_integer(d)) < 0);
            }
            have round_down != 0 and 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                intro();
                assumption();
            }
            have round_down == 0 and 0 < truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1 by {
                intro();
                contradiction(round_down == 0);
            }
            have round_down == 0 and truncating_remainder(to_integer(n), to_integer(d)) <= 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                intro();
                contradiction(truncating_remainder(to_integer(n), to_integer(d)) <= 0);
            }
            have truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1 by {
                intro();
                contradiction(truncating_remainder(to_integer(n), to_integer(d)) < 0);
            }
            have 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                intro();
                assumption();
            }
            apply(integer_floor_from_remainder(to_integer(n), to_integer(d), truncating_quotient(to_integer(n), to_integer(d)), truncating_remainder(to_integer(n), to_integer(d)), to_integer(result)));
            have round_down != 0 implies to_integer(result) * to_integer(d) <= to_integer(n) by {
                intro();
                assumption();
            }
            have round_down != 0 implies to_integer(n) < (to_integer(result) + 1) * to_integer(d) by {
                intro();
                assumption();
            }
            have round_down == 0 implies to_integer(n) <= to_integer(result) * to_integer(d) by {
                intro();
                contradiction(round_down == 0);
            }
            have round_down == 0 implies (to_integer(result) + -1) * to_integer(d) < to_integer(n) by {
                intro();
                contradiction(round_down == 0);
            }
            simp();
        }
    } else {
        if mod < 0 {
            apply(int32_less_than_to_integer(mod, 0));
            apply(integer_lower_correction_bound(to_integer(n), to_integer(d), to_integer(quot), to_integer(mod), -9223372036854775808));
            apply(int64_less_equal_of_to_integer(-9223372036854775807i64, quot));
            have defined(quot + -1i64) by simp;
            apply(int64_add_to_integer(quot, -1i64));
            have -9223372036854775808 <= to_integer(quot + -1i64) by { arithmetic() using {
                to_integer(quot + -1i64) == to_integer(quot) + -1;
                -9223372036854775807 <= to_integer(quot); to_integer(quot) <= 9223372036854775807;
            } }
            have to_integer(quot + -1i64) <= 9223372036854775807 by { arithmetic() using {
                to_integer(quot + -1i64) == to_integer(quot) + -1;
                -9223372036854775807 <= to_integer(quot); to_integer(quot) <= 9223372036854775807;
            } }
            have to_integer(quot + -1i64) == truncating_quotient(to_integer(n), to_integer(d)) + -1 by {
                rewrite(to_integer(quot + -1i64) == to_integer(quot) + -1);
                rewrite(to_integer(quot) == truncating_quotient(to_integer(n), to_integer(d)));
                simp();
            }

            have truncating_remainder(to_integer(n), to_integer(d)) < 0 by {
                rewrite(truncating_remainder(to_integer(n), to_integer(d)) == to_integer(mod));
                arithmetic() using { to_integer(mod) < 0; }
            }
            have not (0 <= truncating_remainder(to_integer(n), to_integer(d))) by {
                rewrite(truncating_remainder(to_integer(n), to_integer(d)) == to_integer(mod));
                arithmetic() using { to_integer(mod) < 0; }
            }
            have not (0 < truncating_remainder(to_integer(n), to_integer(d))) by {
                rewrite(truncating_remainder(to_integer(n), to_integer(d)) == to_integer(mod));
                arithmetic() using { to_integer(mod) < 0; }
            }
            have truncating_remainder(to_integer(n), to_integer(d)) <= 0 by {
                rewrite(truncating_remainder(to_integer(n), to_integer(d)) == to_integer(mod));
                arithmetic() using { to_integer(mod) < 0; }
            }
            if round_down == 0 {
                execute();
                have -9223372036854775808 <= to_integer(result) by simp;
                have to_integer(result) <= 9223372036854775807 by simp;
                apply(int64_less_equal_of_to_integer(-9223372036854775808i64, result));
                apply(int64_less_equal_of_to_integer(result, 9223372036854775807i64));
                have to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by simp;
                have round_down != 0 and truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1 by {
                    intro();
                    contradiction(round_down == 0);
                }
                have round_down != 0 and 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                    intro();
                    contradiction(0 <= truncating_remainder(to_integer(n), to_integer(d)));
                }
                have round_down == 0 and 0 < truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1 by {
                    intro();
                    contradiction(0 < truncating_remainder(to_integer(n), to_integer(d)));
                }
                have round_down == 0 and truncating_remainder(to_integer(n), to_integer(d)) <= 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                    intro();
                    assumption();
                }
                have 0 < truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1 by {
                    intro();
                    contradiction(0 < truncating_remainder(to_integer(n), to_integer(d)));
                }
                have truncating_remainder(to_integer(n), to_integer(d)) <= 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                    intro();
                    assumption();
                }
                apply(integer_ceiling_from_remainder(to_integer(n), to_integer(d), truncating_quotient(to_integer(n), to_integer(d)), truncating_remainder(to_integer(n), to_integer(d)), to_integer(result)));
                have round_down != 0 implies to_integer(result) * to_integer(d) <= to_integer(n) by {
                    intro();
                    contradiction(round_down == 0);
                }
                have round_down != 0 implies to_integer(n) < (to_integer(result) + 1) * to_integer(d) by {
                    intro();
                    contradiction(round_down == 0);
                }
                have round_down == 0 implies to_integer(n) <= to_integer(result) * to_integer(d) by {
                    intro();
                    assumption();
                }
                have round_down == 0 implies (to_integer(result) + -1) * to_integer(d) < to_integer(n) by {
                    intro();
                    assumption();
                }
                simp();
            } else {
                execute();
                have -9223372036854775808 <= to_integer(result) by simp;
                have to_integer(result) <= 9223372036854775807 by simp;
                apply(int64_less_equal_of_to_integer(-9223372036854775808i64, result));
                apply(int64_less_equal_of_to_integer(result, 9223372036854775807i64));
                have to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1 by simp;
                have round_down != 0 and truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1 by {
                    intro();
                    assumption();
                }
                have round_down != 0 and 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                    intro();
                    contradiction(0 <= truncating_remainder(to_integer(n), to_integer(d)));
                }
                have round_down == 0 and 0 < truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1 by {
                    intro();
                    contradiction(0 < truncating_remainder(to_integer(n), to_integer(d)));
                }
                have round_down == 0 and truncating_remainder(to_integer(n), to_integer(d)) <= 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                    intro();
                    contradiction(round_down == 0);
                }
                have truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1 by {
                    intro();
                    assumption();
                }
                have 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                    intro();
                    contradiction(0 <= truncating_remainder(to_integer(n), to_integer(d)));
                }
                apply(integer_floor_from_remainder(to_integer(n), to_integer(d), truncating_quotient(to_integer(n), to_integer(d)), truncating_remainder(to_integer(n), to_integer(d)), to_integer(result)));
                have round_down != 0 implies to_integer(result) * to_integer(d) <= to_integer(n) by {
                    intro();
                    assumption();
                }
                have round_down != 0 implies to_integer(n) < (to_integer(result) + 1) * to_integer(d) by {
                    intro();
                    assumption();
                }
                have round_down == 0 implies to_integer(n) <= to_integer(result) * to_integer(d) by {
                    intro();
                    contradiction(round_down == 0);
                }
                have round_down == 0 implies (to_integer(result) + -1) * to_integer(d) < to_integer(n) by {
                    intro();
                    contradiction(round_down == 0);
                }
                simp();
            }
        } else {
            apply(int32_not_lt_implies_ge(mod, 0));
            apply(int32_ge_implies_reversed_le(mod, 0));
            apply(int32_not_lt_implies_ge(0, mod));
            apply(int32_ge_implies_reversed_le(0, mod));
            apply(int32_le_and_not_lt_implies_eq(mod, 0));
            apply(int32_less_equal_to_integer(0, mod));
            apply(int32_less_equal_to_integer(mod, 0));
            have not (truncating_remainder(to_integer(n), to_integer(d)) < 0) by {
                rewrite(truncating_remainder(to_integer(n), to_integer(d)) == to_integer(mod));
                arithmetic() using { 0 <= to_integer(mod); to_integer(mod) <= 0; }
            }
            have 0 <= truncating_remainder(to_integer(n), to_integer(d)) by {
                rewrite(truncating_remainder(to_integer(n), to_integer(d)) == to_integer(mod));
                arithmetic() using { 0 <= to_integer(mod); to_integer(mod) <= 0; }
            }
            have not (0 < truncating_remainder(to_integer(n), to_integer(d))) by {
                rewrite(truncating_remainder(to_integer(n), to_integer(d)) == to_integer(mod));
                arithmetic() using { 0 <= to_integer(mod); to_integer(mod) <= 0; }
            }
            have truncating_remainder(to_integer(n), to_integer(d)) <= 0 by {
                rewrite(truncating_remainder(to_integer(n), to_integer(d)) == to_integer(mod));
                arithmetic() using { 0 <= to_integer(mod); to_integer(mod) <= 0; }
            }
            if round_down == 0 {
                execute();
                have -9223372036854775808 <= to_integer(result) by simp;
                have to_integer(result) <= 9223372036854775807 by simp;
                apply(int64_less_equal_of_to_integer(-9223372036854775808i64, result));
                apply(int64_less_equal_of_to_integer(result, 9223372036854775807i64));
                have to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by simp;
                have round_down != 0 and truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1 by {
                    intro();
                    contradiction(truncating_remainder(to_integer(n), to_integer(d)) < 0);
                }
                have round_down != 0 and 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                    intro();
                    contradiction(round_down == 0);
                }
                have round_down == 0 and 0 < truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1 by {
                    intro();
                    contradiction(0 < truncating_remainder(to_integer(n), to_integer(d)));
                }
                have round_down == 0 and truncating_remainder(to_integer(n), to_integer(d)) <= 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                    intro();
                    assumption();
                }
                have 0 < truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1 by {
                    intro();
                    contradiction(0 < truncating_remainder(to_integer(n), to_integer(d)));
                }
                have truncating_remainder(to_integer(n), to_integer(d)) <= 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                    intro();
                    assumption();
                }
                apply(integer_ceiling_from_remainder(to_integer(n), to_integer(d), truncating_quotient(to_integer(n), to_integer(d)), truncating_remainder(to_integer(n), to_integer(d)), to_integer(result)));
                have round_down != 0 implies to_integer(result) * to_integer(d) <= to_integer(n) by {
                    intro();
                    contradiction(round_down == 0);
                }
                have round_down != 0 implies to_integer(n) < (to_integer(result) + 1) * to_integer(d) by {
                    intro();
                    contradiction(round_down == 0);
                }
                have round_down == 0 implies to_integer(n) <= to_integer(result) * to_integer(d) by {
                    intro();
                    assumption();
                }
                have round_down == 0 implies (to_integer(result) + -1) * to_integer(d) < to_integer(n) by {
                    intro();
                    assumption();
                }
                simp();
            } else {
                execute();
                have -9223372036854775808 <= to_integer(result) by simp;
                have to_integer(result) <= 9223372036854775807 by simp;
                apply(int64_less_equal_of_to_integer(-9223372036854775808i64, result));
                apply(int64_less_equal_of_to_integer(result, 9223372036854775807i64));
                have to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by simp;
                have round_down != 0 and truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1 by {
                    intro();
                    contradiction(truncating_remainder(to_integer(n), to_integer(d)) < 0);
                }
                have round_down != 0 and 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                    intro();
                    assumption();
                }
                have round_down == 0 and 0 < truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1 by {
                    intro();
                    contradiction(0 < truncating_remainder(to_integer(n), to_integer(d)));
                }
                have round_down == 0 and truncating_remainder(to_integer(n), to_integer(d)) <= 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                    intro();
                    contradiction(round_down == 0);
                }
                have truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1 by {
                    intro();
                    contradiction(truncating_remainder(to_integer(n), to_integer(d)) < 0);
                }
                have 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                    intro();
                    assumption();
                }
                apply(integer_floor_from_remainder(to_integer(n), to_integer(d), truncating_quotient(to_integer(n), to_integer(d)), truncating_remainder(to_integer(n), to_integer(d)), to_integer(result)));
                have round_down != 0 implies to_integer(result) * to_integer(d) <= to_integer(n) by {
                    intro();
                    assumption();
                }
                have round_down != 0 implies to_integer(n) < (to_integer(result) + 1) * to_integer(d) by {
                    intro();
                    assumption();
                }
                have round_down == 0 implies to_integer(n) <= to_integer(result) * to_integer(d) by {
                    intro();
                    contradiction(round_down == 0);
                }
                have round_down == 0 implies (to_integer(result) + -1) * to_integer(d) < to_integer(n) by {
                    intro();
                    contradiction(round_down == 0);
                }
                simp();
            }
        }
    }
}
