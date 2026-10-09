# arithmetic reduces order premises under an untouched goal

The listed equality is eliminated by solving it for the smallest atom it
mentions, here `to_integer(i)`. The goal does not mention that atom, so
eliminating changes nothing in it. The order premises do mention it, and
only after they are reduced the same way do they bound the goal's own atom:
`to_integer(i + 5u64) - 5 < to_integer(n)` and `to_integer(n) <= 100`.

The planner used to stop when elimination left the goal as it was, on the
ground that the direct routes had already seen that claim. They had seen it
beside the unreduced premises.

```click
theorem bounded(i: uint64, n: uint64) {
    requires to_integer(i) < to_integer(n);
    requires to_integer(n) <= 100;
    requires to_integer(i + 5u64) == to_integer(i) + 5;
    ensures to_integer(i + 5u64) < 200 by {
        arithmetic() using {
            to_integer(i) < to_integer(n);
            to_integer(n) <= 100;
            to_integer(i + 5u64) == to_integer(i) + 5;
        }
    }
}
```

```expect
pass
```
