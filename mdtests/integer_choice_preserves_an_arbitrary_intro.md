# Logical choices remain independent of universal witnesses

```click
theorem independent_integer_choice() {
    requires exists (x: Integer) { x == 0 };
    ensures forall (arbitrary: Integer) {
        exists (found: Integer) { found == 0 and arbitrary == arbitrary }
    } by {
        intro();
        let chosen = obtain(exists (chosen: Integer) { chosen == 0 });
        have arbitrary == arbitrary by { known(); }
        witness(chosen);
        known();
    }
}
```

```expect
pass
```
