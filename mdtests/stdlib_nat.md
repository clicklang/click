# stdlib nat

```click
theorem nat_laws(a: Nat, b: Nat, c: Nat) {
    ensures nat::add(Nat::Zero, a) == a by apply(nat::add_left_identity(a));
    ensures nat::add(a, Nat::Zero) == a by apply(nat::add_right_identity(a));
    ensures nat::add(Nat::Succ(a), b) == Nat::Succ(nat::add(a, b)) by apply(nat::add_succ_left(a, b));
    ensures nat::add(a, Nat::Succ(b)) == Nat::Succ(nat::add(a, b)) by apply(nat::add_succ_right(a, b));
    ensures nat::add(nat::add(a, b), c) == nat::add(a, nat::add(b, c)) by apply(nat::add_associative(a, b, c));
    ensures nat::add(a, b) == nat::add(b, a) by apply(nat::add_commutative(a, b));
}

theorem one_plus_one() {
    ensures nat::add(Nat::Succ(Nat::Zero), Nat::Succ(Nat::Zero))
        == Nat::Succ(Nat::Succ(Nat::Zero)) by {
        unfold(nat::add(Nat::Succ(Nat::Zero), Nat::Succ(Nat::Zero)));
        unfold(nat::add(Nat::Zero, Nat::Succ(Nat::Zero)));
        simp();
    }
}
```

```expect
pass
```
