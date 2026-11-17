# Pure Integer existential elimination retains a checked symbolic witness

```click
theorem integer_exists_choose() {
    requires exists (z: Integer) { z == z };
    ensures exists (k: Integer) { k == k } by {
        let candidate = obtain(exists (k: Integer) { k == k });
        witness(candidate);
        known();
    }
}

theorem integer_exists_from_have() {
    ensures exists (z: Integer) { z == 0 } by {
        have exists (x: Integer) { x == 0 } by {
            witness(0);
            normalize();
        }
        let candidate = obtain(exists (candidate: Integer) { candidate == 0 });
        witness(candidate);
        known();
    }
}

theorem integer_exists_multiple_bindings() {
    requires exists (x: Integer, y: Integer) { x == y };
    ensures exists (a: Integer, b: Integer) { a == b } by {
        let (left, right) = obtain(exists (x: Integer, y: Integer) { x == y });
        witness(left);
        witness(right);
        known();
    }
}

theorem integer_exists_open_one() {
    requires exists (x: Integer, y: Integer) { x < y };
    ensures exists (x: Integer, y: Integer) { x < y } by {
        let left = obtain(exists (x: Integer, y: Integer) { x < y });
        let right = obtain(exists (y: Integer) { left < y });
        witness(left, right);
        known();
    }
}
```

```expect
pass
```
