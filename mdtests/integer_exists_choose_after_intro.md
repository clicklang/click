# Integer let-satisfy freshens against an introduced ambient binder

```click
theorem integer_exists_choose_after_intro() {
    requires exists (z: Integer) { z == z };
    ensures forall (q: Integer) { exists (k: Integer) { k == k } } by {
        intro() {
            let candidate = obtain(exists (candidate: Integer) { candidate == candidate });
            witness(candidate);
            close();
        }
    }
}
```

```expect
pass
```
