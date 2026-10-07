# Theorem application accepts mirrored order spellings

A mirrored comparison keeps its operands, relation, and strictness. It does
not turn a non-strict bound into a strict bound.

```click
theorem observed_range(x: uint32) {
    ensures 0 <= to_integer(x) by { apply(uint32_to_integer_bounds(x)); }
    ensures to_integer(x) >= 0 by { apply(uint32_to_integer_bounds(x)); }
}
theorem integer_strict_source(x: Integer, y: Integer) {
    requires x < y;
    ensures x < y by { assumption(); }
}
theorem integer_strict_mirrored(x: Integer, y: Integer) {
    requires x < y;
    ensures y > x by {
        apply(integer_strict_source(x, y)) using { x < y; }
    }
}
theorem integer_weak_source(x: Integer, y: Integer) {
    requires x <= y;
    ensures x <= y by { assumption(); }
}
theorem integer_weak_mirrored(x: Integer, y: Integer) {
    requires x <= y;
    ensures y >= x by {
        apply(integer_weak_source(x, y)) using { x <= y; }
    }
}
theorem integer_greater_source(x: Integer, y: Integer) {
    requires x > y;
    ensures x > y by { assumption(); }
}
theorem integer_greater_mirrored(x: Integer, y: Integer) {
    requires x > y;
    ensures y < x by {
        apply(integer_greater_source(x, y)) using { x > y; }
    }
}
theorem integer_greater_equal_source(x: Integer, y: Integer) {
    requires x >= y;
    ensures x >= y by { assumption(); }
}
theorem integer_greater_equal_mirrored(x: Integer, y: Integer) {
    requires x >= y;
    ensures y <= x by {
        apply(integer_greater_equal_source(x, y)) using { x >= y; }
    }
}
theorem int32_strict_source(x: int32, y: int32) {
    requires x < y;
    ensures x < y by { assumption(); }
}
theorem int32_strict_mirrored(x: int32, y: int32) {
    requires x < y;
    ensures y > x by {
        apply(int32_strict_source(x, y)) using { x < y; }
    }
}
theorem int32_weak_source(x: int32, y: int32) {
    requires x <= y;
    ensures x <= y by { assumption(); }
}
theorem int32_weak_mirrored(x: int32, y: int32) {
    requires x <= y;
    ensures y >= x by {
        apply(int32_weak_source(x, y)) using { x <= y; }
    }
}
theorem int32_greater_source(x: int32, y: int32) {
    requires x > y;
    ensures x > y by { assumption(); }
}
theorem int32_greater_mirrored(x: int32, y: int32) {
    requires x > y;
    ensures y < x by {
        apply(int32_greater_source(x, y)) using { x > y; }
    }
}
theorem int32_greater_equal_source(x: int32, y: int32) {
    requires x >= y;
    ensures x >= y by { assumption(); }
}
theorem int32_greater_equal_mirrored(x: int32, y: int32) {
    requires x >= y;
    ensures y <= x by {
        apply(int32_greater_equal_source(x, y)) using { x >= y; }
    }
}
theorem int64_strict_source(x: int64, y: int64) {
    requires x < y;
    ensures x < y by { assumption(); }
}
theorem int64_strict_mirrored(x: int64, y: int64) {
    requires x < y;
    ensures y > x by {
        apply(int64_strict_source(x, y)) using { x < y; }
    }
}
theorem int64_weak_source(x: int64, y: int64) {
    requires x <= y;
    ensures x <= y by { assumption(); }
}
theorem int64_weak_mirrored(x: int64, y: int64) {
    requires x <= y;
    ensures y >= x by {
        apply(int64_weak_source(x, y)) using { x <= y; }
    }
}
theorem int64_greater_source(x: int64, y: int64) {
    requires x > y;
    ensures x > y by { assumption(); }
}
theorem int64_greater_mirrored(x: int64, y: int64) {
    requires x > y;
    ensures y < x by {
        apply(int64_greater_source(x, y)) using { x > y; }
    }
}
theorem int64_greater_equal_source(x: int64, y: int64) {
    requires x >= y;
    ensures x >= y by { assumption(); }
}
theorem int64_greater_equal_mirrored(x: int64, y: int64) {
    requires x >= y;
    ensures y <= x by {
        apply(int64_greater_equal_source(x, y)) using { x >= y; }
    }
}
theorem uint32_strict_source(x: uint32, y: uint32) {
    requires x < y;
    ensures x < y by { assumption(); }
}
theorem uint32_strict_mirrored(x: uint32, y: uint32) {
    requires x < y;
    ensures y > x by {
        apply(uint32_strict_source(x, y)) using { x < y; }
    }
}
theorem uint32_weak_source(x: uint32, y: uint32) {
    requires x <= y;
    ensures x <= y by { assumption(); }
}
theorem uint32_weak_mirrored(x: uint32, y: uint32) {
    requires x <= y;
    ensures y >= x by {
        apply(uint32_weak_source(x, y)) using { x <= y; }
    }
}
theorem uint32_greater_source(x: uint32, y: uint32) {
    requires x > y;
    ensures x > y by { assumption(); }
}
theorem uint32_greater_mirrored(x: uint32, y: uint32) {
    requires x > y;
    ensures y < x by {
        apply(uint32_greater_source(x, y)) using { x > y; }
    }
}
theorem uint32_greater_equal_source(x: uint32, y: uint32) {
    requires x >= y;
    ensures x >= y by { assumption(); }
}
theorem uint32_greater_equal_mirrored(x: uint32, y: uint32) {
    requires x >= y;
    ensures y <= x by {
        apply(uint32_greater_equal_source(x, y)) using { x >= y; }
    }
}
theorem uint64_strict_source(x: uint64, y: uint64) {
    requires x < y;
    ensures x < y by { assumption(); }
}
theorem uint64_strict_mirrored(x: uint64, y: uint64) {
    requires x < y;
    ensures y > x by {
        apply(uint64_strict_source(x, y)) using { x < y; }
    }
}
theorem uint64_weak_source(x: uint64, y: uint64) {
    requires x <= y;
    ensures x <= y by { assumption(); }
}
theorem uint64_weak_mirrored(x: uint64, y: uint64) {
    requires x <= y;
    ensures y >= x by {
        apply(uint64_weak_source(x, y)) using { x <= y; }
    }
}
theorem uint64_greater_source(x: uint64, y: uint64) {
    requires x > y;
    ensures x > y by { assumption(); }
}
theorem uint64_greater_mirrored(x: uint64, y: uint64) {
    requires x > y;
    ensures y < x by {
        apply(uint64_greater_source(x, y)) using { x > y; }
    }
}
theorem uint64_greater_equal_source(x: uint64, y: uint64) {
    requires x >= y;
    ensures x >= y by { assumption(); }
}
theorem uint64_greater_equal_mirrored(x: uint64, y: uint64) {
    requires x >= y;
    ensures y <= x by {
        apply(uint64_greater_equal_source(x, y)) using { x >= y; }
    }
}
```

```expect
pass
```
