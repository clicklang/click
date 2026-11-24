# Algebraic existential witnesses and choices

The smallest proposition needed by the DFS reachability invariant is an
existential over `Nat`. A chosen algebraic witness remains usable as a field
of a later constructor witness.

```click
theorem nat_zero_exists() {
    ensures exists (fuel: Nat) { fuel == Nat::Zero } by {
        witness(Nat::Zero);
        close();
    }
}

theorem nat_successor_exists() {
    requires exists (fuel: Nat) { fuel == Nat::Zero };
    ensures exists (next: Nat) { next == Nat::Succ(Nat::Zero) } by {
        let fuel = obtain(exists (fuel: Nat) { fuel == Nat::Zero });
        witness(Nat::Succ(fuel));
        rewrite(fuel, Nat::Zero);
        close();
    }
}

theorem nat_reflexive_forall() {
    ensures forall (value: Nat) { value == value } by {
        intro();
        close();
    }
}
```

```expect
pass
```
