# Pure Integer existential elimination retains a checked symbolic witness

```click
theorem integer_exists_choose() {
    requires exists (z: Integer) { z == z };
    ensures exists (k: Integer) { k == k } by {
        obtain (candidate: Integer) { candidate == candidate }
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
        obtain (candidate: Integer) { candidate == 0 }
        witness(candidate);
        known();
    }
}

theorem integer_exists_multiple_bindings() {
    requires exists (x: Integer, y: Integer) { x == y };
    ensures exists (a: Integer, b: Integer) { a == b } by {
        obtain (left: Integer, right: Integer) { left == right }
        witness(left);
        witness(right);
        known();
    }
}
```

```expect
pass
```
