# Arithmetic is defined for the selected witness

```click
theorem subtract_witness() {
    ensures exists (k: int32) { to_integer(k - 1) == -1 }
        by { witness(0); close(); }
}
theorem multiply_witness() {
    ensures exists (k: int64) { to_integer(k * 2i64) == 4 }
        by { witness(2i64); close(); }
}
theorem divide_witness() {
    ensures exists (k: int32) { to_integer(6 / k) == 3 }
        by { witness(2); close(); }
}
theorem remainder_witness() {
    ensures exists (k: uint64) { to_integer(7u64 % k) == 1 }
        by { witness(2u64); close(); }
}
```

```expect
pass
```
