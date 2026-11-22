import click::integer;

// Scalar bounds for a nonempty int32 array fold and its induction prefix.
theorem array_fold_induction_bounds(lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    requires hi <= 1073741823;
    ensures 0 <= to_integer(hi - 1) and
            to_integer(hi - 1) < to_integer(hi) and
            to_integer(lo) <= to_integer(hi - 1) and
            0 <= to_integer(hi - lo) and
            to_integer(hi - 1) <= 1073741823 and
            to_integer(hi - lo) <= 1073741823 and
            0 <= to_integer(hi - 1 - lo) and
            to_integer(hi - 1 - lo) <= 1073741823 and
            to_integer(hi - 1) < 2147483647 by {
        have 1 <= hi by { solve() using { 0 <= lo; lo < hi; }; }
        have lo <= hi by { solve() using { lo < hi; }; }
        have defined(hi - 1) by {
            apply(integer::int32_nonnegative_subtract_within_value_is_defined(hi, 1));
        }
        have defined(hi - lo) by {
            apply(integer::int32_nonnegative_subtract_within_value_is_defined(hi, lo));
        }
        have to_integer(hi - 1) == to_integer(hi) - 1 by {
            apply(integer::int32_subtract_to_integer(hi, 1));
        }
        have to_integer(hi - lo) == to_integer(hi) - to_integer(lo) by {
            apply(integer::int32_subtract_to_integer(hi, lo));
        }
        have to_integer(lo) <= to_integer(hi - 1) by {
            rewrite(to_integer(hi - 1), to_integer(hi) - 1);
            solve() using { lo < hi; };
        }
        have -2147483648 <= to_integer(hi - 1) - to_integer(lo) by {
            solve() using { defined(hi - 1); to_integer(lo) <= to_integer(hi - 1); };
        }
        have to_integer(hi - 1) - to_integer(lo) <= 2147483647 by {
            rewrite(to_integer(hi - 1), to_integer(hi) - 1);
            solve() using { 0 <= lo; hi <= 1073741823; };
        }
        have defined(hi - 1 - lo) by { known(); }
        have to_integer(hi - 1 - lo) == to_integer(hi - 1) - to_integer(lo) by {
            apply(integer::int32_subtract_to_integer(hi - 1, lo));
        }
        have 0 <= to_integer(hi - 1) by {
            rewrite(to_integer(hi - 1), to_integer(hi) - 1);
            solve() using { 1 <= hi; };
        }
        have to_integer(hi - 1) < to_integer(hi) by {
            rewrite(to_integer(hi - 1), to_integer(hi) - 1);
            known();
        }
        have 0 <= to_integer(hi - lo) by {
            rewrite(to_integer(hi - lo), to_integer(hi) - to_integer(lo));
            solve() using { lo <= hi; };
        }
        have to_integer(hi - 1) <= 1073741823 by {
            rewrite(to_integer(hi - 1), to_integer(hi) - 1);
            solve() using { hi <= 1073741823; };
        }
        have to_integer(hi - lo) <= 1073741823 by {
            rewrite(to_integer(hi - lo), to_integer(hi) - to_integer(lo));
            solve() using { 0 <= lo; hi <= 1073741823; };
        }
        have 0 <= to_integer(hi - 1 - lo) by {
            rewrite(to_integer(hi - 1 - lo), to_integer(hi - 1) - to_integer(lo));
            solve() using { defined(hi - 1); to_integer(lo) <= to_integer(hi - 1); };
        }
        have to_integer(hi - 1 - lo) <= 1073741823 by {
            rewrite(to_integer(hi - 1 - lo), to_integer(hi - 1) - to_integer(lo));
            solve() using { 0 <= lo; to_integer(hi - 1) <= 1073741823; };
        }
        have to_integer(hi - 1) < 2147483647 by {
            solve() using { to_integer(hi - 1) <= 1073741823; };
        }
        known();
    }
}
