# A viewable premise from an earlier point prints that point

A `viewable` fact is checked in one memory, and an object's lifetime can end
between two points, so a fact from an earlier point is not the fact of the same
range now. The premise list prints it with its point,
`at(function.entry, viewable(...))`: written back, that is the premise the
checker holds. Printed bare, it would look like the current-state fact the
proof wrote, which the checker does not hold.

Here the window `p[k..k + 4]` is narrowed at entry, and `rewrite(q == p + k)`
reads that entry fact, so the premise is `at(function.entry, ...)`.

```c filename=a_viewable_premise_from_an_earlier_point_prints_that_point.c
unsigned char last(const unsigned char *p, unsigned long n, unsigned long k)
{
	const unsigned char *q = p + k;
	return q[3];
}
```

```click
verifying "a_viewable_premise_from_an_earlier_point_prints_that_point.c";

uint8 last(const uint8* p, uint64 n, uint64 k) {
    requires 4u64 <= n;
    requires k <= n - 4u64;
    requires n <= 4096u64;
    views p[0..n];
    ensures result == p[k + 3u64];
} by {
    have to_integer(k) <= to_integer(k + 4u64);
    have to_integer(k + 4u64) <= to_integer(n);
    have viewable(p[k..k + 4u64]) by {
        transport(viewable(p[0..n]), viewable(p[k..k + 4u64])) using {
            viewable(p[0..n]);
            0 <= k;
            to_integer(k) <= to_integer(k + 4u64);
            to_integer(k + 4u64) <= to_integer(n);
        };
    }
    step();
    step();
    have viewable(q[0..4]) by {
        rewrite(q == p + k);
        transport(viewable(q[0..(k + 4u64) - k]), viewable(q[0..4])) using {
            viewable(q[0..(k + 4u64) - k]);
        };
    }
    step_until(function.exit);
}
```

```expect
fail: at(function.entry, viewable(q[0..k + 4u64 - k]))
```
