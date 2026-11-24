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
        have to_integer(removed) <= to_integer(whole) by close() using { removed <= whole; };
        have to_integer(restored) <= to_integer(removed) by close() using { restored <= removed; };
        have to_integer(whole) <= to_integer(upper) by close() using { whole <= upper; };
        apply(integer::uint64_subtract_to_integer(whole, removed));
        have to_integer(whole - removed) + to_integer(restored) <= to_integer(upper) by close() using {
            to_integer(whole - removed) == to_integer(whole) - to_integer(removed);
            to_integer(restored) <= to_integer(removed);
            to_integer(whole) <= to_integer(upper);
        };
        have to_integer(upper) <= 18446744073709551615 by close();
        have to_integer(whole - removed) + to_integer(restored) <= 18446744073709551615 by close() using {
            to_integer(whole - removed) + to_integer(restored) <= to_integer(upper);
            to_integer(upper) <= 18446744073709551615;
        };
        apply(integer::uint64_add_to_integer(whole - removed, restored));
        rewrite(to_integer((whole - removed) + (restored)), to_integer(whole - removed) + to_integer(restored));
        close();
    }
    ensures to_integer(restored + (whole - removed)) <= to_integer(upper) by {
        have to_integer(removed) <= to_integer(whole) by close() using { removed <= whole; };
        have to_integer(restored) <= to_integer(removed) by close() using { restored <= removed; };
        have to_integer(whole) <= to_integer(upper) by close() using { whole <= upper; };
        apply(integer::uint64_subtract_to_integer(whole, removed));
        have to_integer(restored) + to_integer(whole - removed) <= to_integer(upper) by close() using {
            to_integer(whole - removed) == to_integer(whole) - to_integer(removed);
            to_integer(restored) <= to_integer(removed);
            to_integer(whole) <= to_integer(upper);
        };
        have to_integer(upper) <= 18446744073709551615 by close();
        have to_integer(restored) + to_integer(whole - removed) <= 18446744073709551615 by close() using {
            to_integer(restored) + to_integer(whole - removed) <= to_integer(upper);
            to_integer(upper) <= 18446744073709551615;
        };
        apply(integer::uint64_add_to_integer(restored, whole - removed));
        rewrite(to_integer((restored) + (whole - removed)), to_integer(restored) + to_integer(whole - removed));
        close();
    }
}
```

```expect
pass
```
