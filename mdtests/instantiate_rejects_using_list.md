# Instantiation has no evidence-list syntax

```click
theorem old_instantiation(x: int32) {
    requires forall (k: int32) { k == k };
    ensures x == x by {
        instantiate(forall (k: int32) { k == k }, x) using {};
    }
}
```

```expect
fail: `instantiate` takes no `using` list
```
