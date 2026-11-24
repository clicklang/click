# Bitwise operands retain native guard comparisons

Each clause introduces its guard premise before checking the selected arm.

```click
theorem guard_and_int32(z: int32, y: int32) {
    ensures ((z & 7) < y) implies (if (z & 7) < y { z } else { 3 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z & 7) < y)) implies (if (z & 7) < y { z } else { 3 }) == 3 by {
        intro() {
            close();
        }
    }
    ensures ((z & 7) == y) implies (if (z & 7) == y { z } else { 3 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z & 7) == y)) implies (if (z & 7) == y { z } else { 3 }) == 3 by {
        intro() {
            close();
        }
    }
}

theorem guard_or_int32(z: int32, y: int32) {
    ensures ((z | 7) < y) implies (if (z | 7) < y { z } else { 3 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z | 7) < y)) implies (if (z | 7) < y { z } else { 3 }) == 3 by {
        intro() {
            close();
        }
    }
    ensures ((z | 7) == y) implies (if (z | 7) == y { z } else { 3 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z | 7) == y)) implies (if (z | 7) == y { z } else { 3 }) == 3 by {
        intro() {
            close();
        }
    }
}

theorem guard_xor_int32(z: int32, y: int32) {
    ensures ((z ^ 7) < y) implies (if (z ^ 7) < y { z } else { 3 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z ^ 7) < y)) implies (if (z ^ 7) < y { z } else { 3 }) == 3 by {
        intro() {
            close();
        }
    }
    ensures ((z ^ 7) == y) implies (if (z ^ 7) == y { z } else { 3 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z ^ 7) == y)) implies (if (z ^ 7) == y { z } else { 3 }) == 3 by {
        intro() {
            close();
        }
    }
}

theorem guard_and_uint32(z: uint32, y: uint32) {
    ensures ((z & 7u32) < y) implies (if (z & 7u32) < y { z } else { 3u32 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z & 7u32) < y)) implies (if (z & 7u32) < y { z } else { 3u32 }) == 3u32 by {
        intro() {
            close();
        }
    }
    ensures ((z & 7u32) == y) implies (if (z & 7u32) == y { z } else { 3u32 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z & 7u32) == y)) implies (if (z & 7u32) == y { z } else { 3u32 }) == 3u32 by {
        intro() {
            close();
        }
    }
}

theorem guard_or_uint32(z: uint32, y: uint32) {
    ensures ((z | 7u32) < y) implies (if (z | 7u32) < y { z } else { 3u32 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z | 7u32) < y)) implies (if (z | 7u32) < y { z } else { 3u32 }) == 3u32 by {
        intro() {
            close();
        }
    }
    ensures ((z | 7u32) == y) implies (if (z | 7u32) == y { z } else { 3u32 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z | 7u32) == y)) implies (if (z | 7u32) == y { z } else { 3u32 }) == 3u32 by {
        intro() {
            close();
        }
    }
}

theorem guard_xor_uint32(z: uint32, y: uint32) {
    ensures ((z ^ 7u32) < y) implies (if (z ^ 7u32) < y { z } else { 3u32 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z ^ 7u32) < y)) implies (if (z ^ 7u32) < y { z } else { 3u32 }) == 3u32 by {
        intro() {
            close();
        }
    }
    ensures ((z ^ 7u32) == y) implies (if (z ^ 7u32) == y { z } else { 3u32 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z ^ 7u32) == y)) implies (if (z ^ 7u32) == y { z } else { 3u32 }) == 3u32 by {
        intro() {
            close();
        }
    }
}

theorem guard_and_int64(z: int64, y: int64) {
    ensures ((z & 7i64) < y) implies (if (z & 7i64) < y { z } else { 3i64 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z & 7i64) < y)) implies (if (z & 7i64) < y { z } else { 3i64 }) == 3i64 by {
        intro() {
            close();
        }
    }
    ensures ((z & 7i64) == y) implies (if (z & 7i64) == y { z } else { 3i64 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z & 7i64) == y)) implies (if (z & 7i64) == y { z } else { 3i64 }) == 3i64 by {
        intro() {
            close();
        }
    }
}

theorem guard_or_int64(z: int64, y: int64) {
    ensures ((z | 7i64) < y) implies (if (z | 7i64) < y { z } else { 3i64 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z | 7i64) < y)) implies (if (z | 7i64) < y { z } else { 3i64 }) == 3i64 by {
        intro() {
            close();
        }
    }
    ensures ((z | 7i64) == y) implies (if (z | 7i64) == y { z } else { 3i64 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z | 7i64) == y)) implies (if (z | 7i64) == y { z } else { 3i64 }) == 3i64 by {
        intro() {
            close();
        }
    }
}

theorem guard_xor_int64(z: int64, y: int64) {
    ensures ((z ^ 7i64) < y) implies (if (z ^ 7i64) < y { z } else { 3i64 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z ^ 7i64) < y)) implies (if (z ^ 7i64) < y { z } else { 3i64 }) == 3i64 by {
        intro() {
            close();
        }
    }
    ensures ((z ^ 7i64) == y) implies (if (z ^ 7i64) == y { z } else { 3i64 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z ^ 7i64) == y)) implies (if (z ^ 7i64) == y { z } else { 3i64 }) == 3i64 by {
        intro() {
            close();
        }
    }
}

theorem guard_and_uint64(z: uint64, y: uint64) {
    ensures ((z & 7u64) < y) implies (if (z & 7u64) < y { z } else { 3u64 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z & 7u64) < y)) implies (if (z & 7u64) < y { z } else { 3u64 }) == 3u64 by {
        intro() {
            close();
        }
    }
    ensures ((z & 7u64) == y) implies (if (z & 7u64) == y { z } else { 3u64 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z & 7u64) == y)) implies (if (z & 7u64) == y { z } else { 3u64 }) == 3u64 by {
        intro() {
            close();
        }
    }
}

theorem guard_or_uint64(z: uint64, y: uint64) {
    ensures ((z | 7u64) < y) implies (if (z | 7u64) < y { z } else { 3u64 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z | 7u64) < y)) implies (if (z | 7u64) < y { z } else { 3u64 }) == 3u64 by {
        intro() {
            close();
        }
    }
    ensures ((z | 7u64) == y) implies (if (z | 7u64) == y { z } else { 3u64 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z | 7u64) == y)) implies (if (z | 7u64) == y { z } else { 3u64 }) == 3u64 by {
        intro() {
            close();
        }
    }
}

theorem guard_xor_uint64(z: uint64, y: uint64) {
    ensures ((z ^ 7u64) < y) implies (if (z ^ 7u64) < y { z } else { 3u64 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z ^ 7u64) < y)) implies (if (z ^ 7u64) < y { z } else { 3u64 }) == 3u64 by {
        intro() {
            close();
        }
    }
    ensures ((z ^ 7u64) == y) implies (if (z ^ 7u64) == y { z } else { 3u64 }) == z by {
        intro() {
            close();
        }
    }
    ensures (not ((z ^ 7u64) == y)) implies (if (z ^ 7u64) == y { z } else { 3u64 }) == 3u64 by {
        intro() {
            close();
        }
    }
}

theorem unselected_shift_under_bitwise_guard(z: uint64, y: uint64) {
    requires (z & 7u64) < y;
    ensures (if (z & 7u64) < y { z } else { 1u64 << 64u64 }) == z by {
        close();
    }
}
```

```expect
pass
```
