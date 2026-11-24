# Derive an algebraic existential with the same binder spelling

The implication is available, and its antecedent is a separate exact premise.
This control verifies when the existential binder has the same spelling in the
premise and goal. The alpha-renamed case is in the companion mdtest.

```click
theorem have_algebraic_existential(flag: int32) {
    requires flag != 0;
    requires flag != 0 implies exists (caller_path: Nat) {
        caller_path == Nat::Zero
    };
    ensures exists (caller_path: Nat) {
        caller_path == Nat::Zero
    } by {
        have exists (caller_path: Nat) {
            caller_path == Nat::Zero
        };
        close();
    }
}
```

```expect
pass
```
