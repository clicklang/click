# Apply an established implication

Named facts and written implications use the same `apply` tactic as theorems.
The bare form proves each antecedent; `using` supplies explicit evidence.

```click
theorem named_fact(x: int32, y: int32) {
    requires x > 0;
    requires x > 0 implies y > 0;
    ensures y > 0 by {
        have h: x > 0 implies y > 0 by known();
        apply(h);
    }
}

theorem named_fact_explicit(x: int32, y: int32) {
    requires x > 0;
    requires x > 0 implies y > 0;
    ensures y > 0 by {
        have h: x > 0 implies y > 0 by known();
        apply(h) using { x > 0; };
    }
}

theorem explicit_chain(x: int32, y: int32, z: int32) {
    requires x > 0;
    requires y > 0;
    requires x > 0 implies y > 0 implies z > 0;
    ensures z > 0 by {
        apply(x > 0 implies y > 0 implies z > 0) using { x > 0; y > 0; };
    }
}

theorem solve_antecedent(x: int32, y: int32) {
    requires x > 1;
    requires x > 0 implies y > 0;
    ensures y > 0 by {
        apply(x > 0 implies y > 0);
    }
}

theorem continue_after_application(x: int32, y: int32, z: int32) {
    requires x > 0;
    requires x > 0 implies (y > 0 and z > 0);
    ensures y > 0 by {
        apply(x > 0 implies (y > 0 and z > 0)) using { x > 0; };
        have z > 0 by known();
        known();
    }
}

theorem quantified_conclusion(x: int32) {
    requires x > 0;
    requires x > 0 implies forall (k: int32) { k == k };
    ensures forall (k: int32) { k == k } by {
        apply(x > 0 implies forall (k: int32) { k == k }) using { x > 0; };
    }
}

theorem conjunctive_evidence(x: int32, y: int32, z: int32) {
    requires x > 0 and y > 0;
    requires (x > 0 and y > 0) implies z > 0;
    ensures z > 0 by {
        apply((x > 0 and y > 0) implies z > 0) using { x > 0; y > 0; };
    }
}

```

```expect
pass
```
