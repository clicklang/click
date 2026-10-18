# Restoring part of a non-wrapping unsigned difference preserves its upper bound

The addition restores at most the amount removed. Both operations retain their
full-width values; dropping either bound would admit wraparound or overshoot.

```click
theorem partial_restoration(whole: uint64, removed: uint64, restored: uint64, upper: uint64) {
    requires removed <= whole;
    requires restored <= removed;
    requires whole <= upper;
    ensures (whole - removed) + restored <= upper by {
        normalize() using { removed <= whole; restored <= removed; whole <= upper; };
    }
    ensures restored + (whole - removed) <= upper by {
        normalize() using { removed <= whole; restored <= removed; whole <= upper; };
    }
}
```

```expect
pass
```
