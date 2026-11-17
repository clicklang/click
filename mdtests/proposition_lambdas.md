# Proposition-valued lambdas and range methods

```click
theorem direct_proposition_lambda(x: Integer) {
    ensures (|value: Integer| -> Prop { value == value })(x) by solve();
}

theorem range_lambda_values(lo: int32, hi: int32, limit: int32) {
    let below: fn(int32) -> Prop = |k: int32| -> Prop { k < limit };
    requires hi <= limit;
    ensures (lo..hi).all(below) by { let k = intro(); intro(); solve(); }
}
theorem quantified_proposition_lambdas(value: Integer) {
    ensures (|x: Integer| -> Prop { forall (y: Integer) { x + y == y + x } })(value) by {
        intro();
        solve();
    }
    ensures (|x: Integer| -> Prop { exists (y: Integer) { y == x } })(value) by {
        witness(value);
        solve();
    }
}

theorem local_proposition_values(value: Integer) {
    let reflexive: Prop = prop { value == value };
    ensures reflexive by solve();
}

theorem proposition_connectives(value: Integer) {
    ensures (|x: Integer| -> Prop { x == x and not (x != x) })(value) by solve();
    ensures (|| -> Prop { true })() by solve();
}

theorem existential_range_lambda(lo: int32, hi: int32) {
    let same = |x: int32| -> Prop { x == lo };
    requires lo < hi;
    ensures (lo..hi).any(same) by {
        witness(lo);
        solve();
    }
}

theorem wide_range_predicates(lo: uint64, hi: uint64) {
    let identity: fn(uint64) -> Prop = |x: uint64| -> Prop { x == x };
    requires lo < hi;
    ensures (lo..hi).all(identity) by { let index = intro(); intro(); solve(); }
    ensures (lo..hi).any(identity) by { witness(lo); solve(); }
}

function captured_predicate(limit: int32, value: int32) -> Integer {
    let below = |x: int32| -> Prop { x < limit };
    let limit: int32 = 0;
    if below(value) { 1 } else { 0 }
}

theorem proposition_capture_is_lexical() {
    ensures captured_predicate(5, 3) == 1 by {
        unfold(captured_predicate(5, 3));
        solve();
    }
}

theorem proposition_application_values(value: Integer) {
    let reflexive = |x: Integer| -> Prop { x == x };
    let claim = reflexive(value);
    ensures claim by solve();
}

predicate positive(value: int32) { value > 0 }

theorem proposition_literal_with_predicate(value: int32) {
    requires value > 0;
    ensures prop { positive(value) } by {
        unfold(positive(value));
        solve();
    }
}

```

```expect
pass
```
