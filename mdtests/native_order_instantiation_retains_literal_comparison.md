# Instantiating native orders retains the comparison named by contradiction

```click
theorem signed_instance(x: int32) {
    requires forall (k: int32) { 2 <= k and k < 4 };
    ensures x <= 0 by {
        instantiate(forall (k: int32) { 2 <= k and k < 4 }, 4);
        have not (4 < 4) by { close(); }
        close();
    }
}

theorem unsigned_instance(x: uint64) {
    requires forall (k: uint64) { 2u64 <= k and k < 4u64 };
    ensures x <= 0u64 by {
        instantiate(forall (k: uint64) { 2u64 <= k and k < 4u64 }, 4u64);
        have not (4u64 < 4u64) by { close(); }
        close();
    }
}
```

```expect
pass
```
