# region-relative indexed read

A composite region owns `[start, end)` of its backing array. A nonnegative
relative index whose translated absolute index is below `end` must authorize
the corresponding one-cell read in both proof planning and kernel
certification.

```c filename=region_read.c
struct region {
    int32* data;
    int32 start;
    int32 end;
};

int32 region_read(struct region* region, int32 index) {
    return region->data[region->start + index];
}
```

```click
resource live_region(region: struct region*) {
    owns *region;
    owns region->data[region->start..region->end];
}

verifying "region_read.c";

int32 region_read(struct region* region, int32 index) {
    requires 0 <= index;
    requires defined(region->start + index) and
        to_integer(region->start + index) < to_integer(region->end);
    views live_region(region);
    ensures result == region->data[region->start + index];
} by {
    unfold(live_region(region));
    have defined(region->start + index) by {
        solve() using {
            defined(region->start + index) and
                to_integer(region->start + index) < to_integer(region->end);
        };
    }
    have to_integer(region->start + index) < to_integer(region->end) by {
        solve() using {
            defined(region->start + index) and
                to_integer(region->start + index) < to_integer(region->end);
        };
    }
    have 0 <= index by {
        assumption();
    }
    have to_integer(region->start) <= to_integer(region->start + index);
    have to_integer(region->start + index + 1) <= to_integer(region->end);
    step();
    solve();
}
```

```expect
pass
```
