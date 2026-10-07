# A literal true disjunction does not require the unused native division

```click
theorem guarded(x: uint32) {
    requires x == 0u32 or 5u32 / x == 1u32;
    ensures 1 == 1 by { simp(); }
}

theorem zero_instance() {
    ensures 1 == 1 by { apply(guarded(0u32)); }
}

theorem known_zero_instance(x: uint32) {
    requires x == 0u32;
    ensures 1 == 1 by { apply(guarded(x)); }
}
```

```expect
pass
```
