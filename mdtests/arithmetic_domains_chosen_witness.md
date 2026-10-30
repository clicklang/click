# Arithmetic is defined for the selected witness

```click
theorem subtract_witness() {
    ensures exists (k: int32) { to_integer(k - 1) == -1 }
        by { witness { k: 0 }; solve(); }
}
theorem multiply_witness() {
    ensures exists (k: int64) { to_integer(k * 2i64) == 4 }
        by { witness { k: 2i64 }; solve(); }
}
theorem divide_witness() {
    ensures exists (k: int32) { to_integer(6 / k) == 3 }
        by { witness { k: 2 }; solve(); }
}
theorem remainder_witness() {
    ensures exists (k: uint64) { to_integer(7u64 % k) == 1 }
        by { witness { k: 2u64 }; solve(); }
}
```

```expect
pass
```
