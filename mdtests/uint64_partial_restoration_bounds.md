# Restoring part of a non-wrapping unsigned difference preserves its upper bound

The addition restores at most the amount removed. Both operations retain their
full-width values; dropping either bound would admit wraparound or overshoot.

```click
import click::integer;

theorem partial_restoration(whole: uint64, removed: uint64, restored: uint64, upper: uint64) {
    requires removed <= whole;
    requires restored <= removed;
    requires whole <= upper;
    ensures to_integer((whole - removed) + restored) <= to_integer(upper) by {
        have to_integer(removed) <= to_integer(whole) by solve() using { removed <= whole; };
        have to_integer(restored) <= to_integer(removed) by solve() using { restored <= removed; };
        have to_integer(whole) <= to_integer(upper) by solve() using { whole <= upper; };
        apply(integer::uint64_subtract_to_integer(whole, removed)) using { to_integer(removed) <= to_integer(whole); };
        have to_integer(whole - removed) + to_integer(restored) <= to_integer(upper) by solve() using {
            to_integer(whole - removed) == to_integer(whole) - to_integer(removed);
            to_integer(restored) <= to_integer(removed);
            to_integer(whole) <= to_integer(upper);
        };
        have to_integer(upper) <= 18446744073709551615 by known();
        have to_integer(whole - removed) + to_integer(restored) <= 18446744073709551615 by solve() using {
            to_integer(whole - removed) + to_integer(restored) <= to_integer(upper);
            to_integer(upper) <= 18446744073709551615;
        };
        apply(integer::uint64_add_to_integer(whole - removed, restored)) using { to_integer(whole - removed) + to_integer(restored) <= 18446744073709551615; };
        rewrite(to_integer((whole - removed) + (restored)), to_integer(whole - removed) + to_integer(restored));
        known();
    }
    ensures to_integer(restored + (whole - removed)) <= to_integer(upper) by {
        have to_integer(removed) <= to_integer(whole) by solve() using { removed <= whole; };
        have to_integer(restored) <= to_integer(removed) by solve() using { restored <= removed; };
        have to_integer(whole) <= to_integer(upper) by solve() using { whole <= upper; };
        apply(integer::uint64_subtract_to_integer(whole, removed)) using { to_integer(removed) <= to_integer(whole); };
        have to_integer(restored) + to_integer(whole - removed) <= to_integer(upper) by solve() using {
            to_integer(whole - removed) == to_integer(whole) - to_integer(removed);
            to_integer(restored) <= to_integer(removed);
            to_integer(whole) <= to_integer(upper);
        };
        have to_integer(upper) <= 18446744073709551615 by known();
        have to_integer(restored) + to_integer(whole - removed) <= 18446744073709551615 by solve() using {
            to_integer(restored) + to_integer(whole - removed) <= to_integer(upper);
            to_integer(upper) <= 18446744073709551615;
        };
        apply(integer::uint64_add_to_integer(restored, whole - removed)) using { to_integer(restored) + to_integer(whole - removed) <= 18446744073709551615; };
        rewrite(to_integer((restored) + (whole - removed)), to_integer(restored) + to_integer(whole - removed));
        known();
    }
}
```

```expect
pass
```
