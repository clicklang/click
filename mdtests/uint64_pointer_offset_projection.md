# Native unsigned pointer offsets retain their checked full value

The explicit full-width bound makes the signed low-word projection exact.
This address equality grants no backing-memory authority.

```click
theorem bounded(pointer: int32*, index: uint64) {
    requires index <= 1073741823u64;
    ensures pointer + index as int32 == pointer + index by {
        solve() using { index <= 1073741823u64; };
    }
}
theorem widest(pointer: int32*, index: uint64) {
    requires index <= 2147483647u64;
    ensures pointer + index == pointer + index as int32 by {
        solve() using { index <= 2147483647u64; };
    }
}
theorem strict(pointer: int32*, index: uint64) {
    requires index < 2147483648u64;
    ensures pointer + index as int32 == pointer + index by {
        solve() using { index < 2147483648u64; };
    }
}
```

```expect
pass
```
