import click::integer;

verifying "bitcoin-src/src/util/feefrac.h";
static int64 FeeFrac::Div(int128 n, int32 d, bool round_down) {
    requires round_down == true;
    requires -9223372036854775808 * to_integer(d) <= to_integer(n);
    requires to_integer(n) < 9223372036854775808 * to_integer(d);
    requires d > 0;
    requires d <= 2147483647;
    ensures -9223372036854775808 <= to_integer(result);
    ensures to_integer(result) <= 9223372036854775807;
    ensures -9223372036854775808i64 <= result;
    ensures result <= 9223372036854775807i64;
    ensures truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1;
    ensures 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d));
    ensures to_integer(result) * to_integer(d) <= to_integer(n);
    ensures to_integer(n) < (to_integer(result) + 1) * to_integer(d);
} by {
    have 1 <= d by { close() using { d > 0; }; }
    have -19807040619342712361531211776 <= to_integer(n) by { close() using {
        -9223372036854775808 * to_integer(d) <= to_integer(n); to_integer(d) <= 2147483647;
    }; }
    have to_integer(n) <= 19807040619342712361531211775 by { close() using {
        to_integer(n) < 9223372036854775808 * to_integer(d); to_integer(d) <= 2147483647;
    }; }
    have to_integer(d) != 0 by { close() using { 1 <= to_integer(d); }; }
    have to_integer(d) != -1 by { close() using { 1 <= to_integer(d); }; }
    step();
    step();
    have -9223372036854775808 <= truncating_quotient(to_integer(n), to_integer(d)) by {
        apply(integer::positive_divisor_quotient_lower(to_integer(n), to_integer(d), -9223372036854775808));
    }
    have truncating_quotient(to_integer(n), to_integer(d)) <= 9223372036854775807 by {
        apply(integer::positive_divisor_quotient_strict_upper(to_integer(n), to_integer(d), 9223372036854775808));
        close() using { truncating_quotient(to_integer(n), to_integer(d)) < 9223372036854775808; };
    }
    have -9223372036854775808 <= to_integer(n / d as int128) by { close() using { to_integer(n / d as int128) == truncating_quotient(to_integer(n), to_integer(d)); -9223372036854775808 <= truncating_quotient(to_integer(n), to_integer(d)); }; }
    have to_integer(n / d as int128) <= 9223372036854775807 by { close() using { to_integer(n / d as int128) == truncating_quotient(to_integer(n), to_integer(d)); truncating_quotient(to_integer(n), to_integer(d)) <= 9223372036854775807; }; }
    have to_integer(quot) == to_integer(n / d as int128) by { close() using { -9223372036854775808 <= to_integer(n / d as int128); to_integer(n / d as int128) <= 9223372036854775807; }; }
    have -9223372036854775808 <= to_integer(quot) by { close() using { to_integer(quot) == to_integer(n / d as int128); -9223372036854775808 <= to_integer(n / d as int128); }; }
    have to_integer(quot) <= 9223372036854775807 by { close() using { to_integer(quot) == to_integer(n / d as int128); to_integer(n / d as int128) <= 9223372036854775807; }; }
    step();
    have -2147483646 <= truncating_remainder(to_integer(n), to_integer(d)) by { close() using { -19807040619342712361531211776 <= to_integer(n); to_integer(n) <= 19807040619342712361531211775; 1 <= to_integer(d); to_integer(d) <= 2147483647; }; }
    have truncating_remainder(to_integer(n), to_integer(d)) <= 2147483646 by { close() using { -19807040619342712361531211776 <= to_integer(n); to_integer(n) <= 19807040619342712361531211775; 1 <= to_integer(d); to_integer(d) <= 2147483647; }; }
    have -2147483646 <= to_integer(n % d as int128) by { close() using { to_integer(n % d as int128) == truncating_remainder(to_integer(n), to_integer(d)); -2147483646 <= truncating_remainder(to_integer(n), to_integer(d)); }; }
    have to_integer(n % d as int128) <= 2147483646 by { close() using { to_integer(n % d as int128) == truncating_remainder(to_integer(n), to_integer(d)); truncating_remainder(to_integer(n), to_integer(d)) <= 2147483646; }; }
    have to_integer(mod) == to_integer(n % d as int128) by { close() using { -2147483646 <= to_integer(n % d as int128); to_integer(n % d as int128) <= 2147483646; }; }
    have -2147483646 <= to_integer(mod) by { close() using { to_integer(mod) == to_integer(n % d as int128); -2147483646 <= to_integer(n % d as int128); }; }
    have to_integer(mod) <= 2147483646 by { close() using { to_integer(mod) == to_integer(n % d as int128); to_integer(n % d as int128) <= 2147483646; }; }
    have 0 < to_integer(d) by { close() using { 1 <= to_integer(d); }; }
    apply(integer::positive_divisor_remainder_lower(to_integer(n), to_integer(d)));
    apply(integer::positive_divisor_remainder_upper(to_integer(n), to_integer(d)));
    apply(integer::truncation_identity(to_integer(n), to_integer(d)));
    have to_integer(quot) == truncating_quotient(to_integer(n), to_integer(d)) by { close() using { to_integer(quot) == to_integer(n / d as int128); to_integer(n / d as int128) == truncating_quotient(to_integer(n), to_integer(d)); }; }
    have to_integer(mod) == truncating_remainder(to_integer(n), to_integer(d)) by { close() using { to_integer(mod) == to_integer(n % d as int128); to_integer(n % d as int128) == truncating_remainder(to_integer(n), to_integer(d)); }; }
    have to_integer(n) == to_integer(quot) * to_integer(d) + to_integer(mod) by {
        rewrite(to_integer(quot), truncating_quotient(to_integer(n), to_integer(d)));
        rewrite(to_integer(mod), truncating_remainder(to_integer(n), to_integer(d)));
        close();
    }

    have defined(quot + 0i64);
    have to_integer(quot + 0i64) == to_integer(quot) + 0;
    have -9223372036854775808 <= to_integer(quot + 0i64) by { close() using {
        to_integer(quot + 0i64) == to_integer(quot) + 0;
        -9223372036854775808 <= to_integer(quot); to_integer(quot) <= 9223372036854775807;
    }; }
    have to_integer(quot + 0i64) <= 9223372036854775807 by { close() using {
        to_integer(quot + 0i64) == to_integer(quot) + 0;
        -9223372036854775808 <= to_integer(quot); to_integer(quot) <= 9223372036854775807;
    }; }
    have to_integer(quot + 0i64) == truncating_quotient(to_integer(n), to_integer(d)) by {
        rewrite(to_integer(quot + 0i64), to_integer(quot) + 0);
        close();
    }
    if 0 < mod {

        have not (truncating_remainder(to_integer(n), to_integer(d)) < 0) by {
            rewrite(truncating_remainder(to_integer(n), to_integer(d)), to_integer(mod));
            close() using { 0 < to_integer(mod); };
        }
        have 0 <= truncating_remainder(to_integer(n), to_integer(d)) by {
            rewrite(truncating_remainder(to_integer(n), to_integer(d)), to_integer(mod));
            close() using { 0 < to_integer(mod); };
        }
        have 0 < truncating_remainder(to_integer(n), to_integer(d)) by {
            rewrite(truncating_remainder(to_integer(n), to_integer(d)), to_integer(mod));
            close() using { 0 < to_integer(mod); };
        }
        have not (truncating_remainder(to_integer(n), to_integer(d)) <= 0) by {
            rewrite(truncating_remainder(to_integer(n), to_integer(d)), to_integer(mod));
            close() using { 0 < to_integer(mod); };
        }
        step_until(function.exit);
        have -9223372036854775808 <= to_integer(result);
        have to_integer(result) <= 9223372036854775807;
        have to_integer(result) == truncating_quotient(to_integer(n), to_integer(d));
        have truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1 by {
            intro();
            contradiction(truncating_remainder(to_integer(n), to_integer(d)) < 0);
        }
        have 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
            intro();
            close();
        }
        apply(integer::floor_from_remainder(to_integer(n), to_integer(d), truncating_quotient(to_integer(n), to_integer(d)), truncating_remainder(to_integer(n), to_integer(d)), to_integer(result)));
        close();
    } else {
        if mod < 0 {
            apply(integer::lower_correction_bound(to_integer(n), to_integer(d), to_integer(quot), to_integer(mod), -9223372036854775808));
            have defined(quot + -1i64);
            have to_integer(quot + -1i64) == to_integer(quot) + -1;
            have -9223372036854775808 <= to_integer(quot + -1i64) by { close() using {
                to_integer(quot + -1i64) == to_integer(quot) + -1;
                -9223372036854775807 <= to_integer(quot); to_integer(quot) <= 9223372036854775807;
            }; }
            have to_integer(quot + -1i64) <= 9223372036854775807 by { close() using {
                to_integer(quot + -1i64) == to_integer(quot) + -1;
                -9223372036854775807 <= to_integer(quot); to_integer(quot) <= 9223372036854775807;
            }; }
            have to_integer(quot + -1i64) == truncating_quotient(to_integer(n), to_integer(d)) + -1 by {
                rewrite(to_integer(quot + -1i64), to_integer(quot) + -1);
                rewrite(to_integer(quot), truncating_quotient(to_integer(n), to_integer(d)));
                close();
            }

            have truncating_remainder(to_integer(n), to_integer(d)) < 0 by {
                rewrite(truncating_remainder(to_integer(n), to_integer(d)), to_integer(mod));
                close() using { to_integer(mod) < 0; };
            }
            have not (0 <= truncating_remainder(to_integer(n), to_integer(d))) by {
                rewrite(truncating_remainder(to_integer(n), to_integer(d)), to_integer(mod));
                close() using { to_integer(mod) < 0; };
            }
            have not (0 < truncating_remainder(to_integer(n), to_integer(d))) by {
                rewrite(truncating_remainder(to_integer(n), to_integer(d)), to_integer(mod));
                close() using { to_integer(mod) < 0; };
            }
            have truncating_remainder(to_integer(n), to_integer(d)) <= 0 by {
                rewrite(truncating_remainder(to_integer(n), to_integer(d)), to_integer(mod));
                close() using { to_integer(mod) < 0; };
            }
            step_until(function.exit);
            have -9223372036854775808 <= to_integer(result);
            have to_integer(result) <= 9223372036854775807;
            have to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1;
            have truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1 by {
                intro();
                close();
            }
            have 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                intro();
                contradiction(0 <= truncating_remainder(to_integer(n), to_integer(d)));
            }
            apply(integer::floor_from_remainder(to_integer(n), to_integer(d), truncating_quotient(to_integer(n), to_integer(d)), truncating_remainder(to_integer(n), to_integer(d)), to_integer(result)));
            close();
        } else {
            have not (truncating_remainder(to_integer(n), to_integer(d)) < 0) by {
                rewrite(truncating_remainder(to_integer(n), to_integer(d)), to_integer(mod));
                close() using { 0 <= to_integer(mod); to_integer(mod) <= 0; };
            }
            have 0 <= truncating_remainder(to_integer(n), to_integer(d)) by {
                rewrite(truncating_remainder(to_integer(n), to_integer(d)), to_integer(mod));
                close() using { 0 <= to_integer(mod); to_integer(mod) <= 0; };
            }
            have not (0 < truncating_remainder(to_integer(n), to_integer(d))) by {
                rewrite(truncating_remainder(to_integer(n), to_integer(d)), to_integer(mod));
                close() using { 0 <= to_integer(mod); to_integer(mod) <= 0; };
            }
            have truncating_remainder(to_integer(n), to_integer(d)) <= 0 by {
                rewrite(truncating_remainder(to_integer(n), to_integer(d)), to_integer(mod));
                close() using { 0 <= to_integer(mod); to_integer(mod) <= 0; };
            }
            step_until(function.exit);
            have -9223372036854775808 <= to_integer(result);
            have to_integer(result) <= 9223372036854775807;
            have to_integer(result) == truncating_quotient(to_integer(n), to_integer(d));
            have truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1 by {
                intro();
                contradiction(truncating_remainder(to_integer(n), to_integer(d)) < 0);
            }
            have 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) by {
                intro();
                close();
            }
            apply(integer::floor_from_remainder(to_integer(n), to_integer(d), truncating_quotient(to_integer(n), to_integer(d)), truncating_remainder(to_integer(n), to_integer(d)), to_integer(result)));
            close();
        }
    }
}
