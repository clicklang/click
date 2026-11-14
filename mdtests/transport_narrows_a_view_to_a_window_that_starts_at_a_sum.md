# Containment narrows a view to a window that starts at a sum

A window `p[a..b]` inside a viewable `p[0..n]` is `b - a` bytes from `a`. When `a` is itself a sum, `k + 3u64`, the window's own listed bounds, `a <= b` and `b <= n`, place it inside the source: the end cannot underflow and stays within the view.

```c filename=transport_narrows_a_view_to_a_window_that_starts_at_a_sum.c
unsigned char first(const unsigned char *p, unsigned long n, unsigned long k)
{
	return p[0];
}
```

```click
verifying "transport_narrows_a_view_to_a_window_that_starts_at_a_sum.c";

uint8 first(const uint8* p, uint64 n, uint64 k) {
    requires 4u64 <= n;
    requires k <= n - 4u64;
    requires n <= 4096u64;
    views p[0..n];
    ensures result == p[0];
} by {
    have 0 <= to_integer(k + 3u64);
    have to_integer(k + 3u64) <= to_integer(k + 4u64);
    have to_integer(k + 4u64) <= to_integer(n);
    have viewable(p[k + 3u64..k + 4u64]) by {
        have contains(memory(p[0u64..n]), memory(p[k + 3u64..k + 4u64])) by {
            apply(click::separation::subrange(p, 0u64, n, k + 3u64, k + 4u64)) using {
                0 <= to_integer(k + 3u64);
                to_integer(k + 3u64) <= to_integer(k + 4u64);
                to_integer(k + 4u64) <= to_integer(n);
            };
        }
        apply(click::separation::viewable_restrict(memory(p[0u64..n]), memory(p[k + 3u64..k + 4u64]))) using {
            viewable(p[0u64..n]);
            contains(memory(p[0u64..n]), memory(p[k + 3u64..k + 4u64]));
        };
    }
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
