# a range viewability call requirement is a statable goal

`need_cells` requires every in-range byte of its argument to be viewable. The
caller can state that requirement itself, ahead of the call, in the
`viewable(p[a..b])` range form — the same spelling
[surface synthesis](../docs/concepts/expansion.md) recovers for an emitted
call requirement over an external-argument pointer. The written ends survive
the round trip: the range is spelled over the parameter's own name rather
than over a base displaced by its start.

The proof splits out the guard for one index, bounds its successor, and
uses containment to justify the one-byte window needed by the call.

```c filename=forall_loadable_range.c
int32 range_probe(uint8 bytes[], int32 len) {
    return need_cells(bytes, len);
}
```

```click
verifying "forall_loadable_range.c";

extern int32 need_cells(uint8 bytes[], int32 len) {
    requires forall (k: int32) {
        0 <= k and k < len implies viewable(bytes[k..k + 1])
    };
    ensures result == 0;
}

int32 range_probe(uint8 bytes[], int32 len) {
    requires viewable(bytes[0..len + 1]);
    ensures result == 0;
} by {
    have forall (k: int32) {
        0 <= k and k < len implies viewable(bytes[k..k + 1])
    } by {
        intro();
        intro();
        have k < len by { close(); }
        have to_integer(k + 1) <= to_integer(len) by {
            apply(click::integer::int32_increment_upper_bound(k, len));
        }
        have to_integer(len) <= to_integer(len + 1) by {
            apply(click::integer::int32_increment_lower_bound(len, len, 2147483647));
        }
        have k <= k + 1 by {
            apply(click::integer::int32_to_integer_less_equal_implies_less_equal(k, k + 1));
        }
        have k + 1 <= len + 1 by {
            apply(click::integer::le_transitive(to_integer(k + 1), to_integer(len), to_integer(len + 1)));
            apply(click::integer::int32_to_integer_less_equal_implies_less_equal(k + 1, len + 1));
        }
        apply(click::separation::contains_subrange(bytes, 0, len + 1, k, k + 1));
        apply(click::separation::viewable_restrict(memory(bytes[0..len + 1]), memory(bytes[k..k + 1])));
        close();
    }
    step_until(function.exit);
    close();
}
```

```expect
pass
```
