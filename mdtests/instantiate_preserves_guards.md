# Instantiation preserves a guarded body without proving its guard

```click
function value(x: int32) -> int32 { x }

theorem instance_without_guard(x: int32) {
    requires forall (k: int32) { k > 0 implies value(k) > 0 };
    ensures x > 0 implies value(x) > 0 by {
        instantiate(forall (k: int32) { k > 0 implies value(k) > 0 }, x);
        known();
    }
}

theorem guard_proved_after_instantiation(x: int32) {
    requires forall (k: int32) { k > 0 implies value(k) > 0 };
    requires x > 1;
    ensures value(x) > 0 by {
        instantiate(forall (k: int32) { k > 0 implies value(k) > 0 }, x);
        have x > 0;
        known();
    }
}

theorem nested_instance_keeps_its_own_guard(x: int32, y: int32) {
    requires forall (k: int32) {
        k >= 0 implies forall (j: int32) { j >= 0 implies value(j) >= 0 }
    };
    requires x >= 0;
    ensures y >= 0 implies value(y) >= 0 by {
        instantiate(forall (k: int32) {
            k >= 0 implies forall (j: int32) { j >= 0 implies value(j) >= 0 }
        }, x);
        instantiate(forall (j: int32) { j >= 0 implies value(j) >= 0 }, y);
        known();
    }
}
```

```expect
pass
```
