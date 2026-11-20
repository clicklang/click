# Pure int32 sequence comparisons keep concatenation

```click
theorem keeps_concatenation(a: int32, b: int32) {
    ensures forall (unused: Integer) {
        [] ++ [a] ++ [b] == [a, b] ++ []
    } by { intro(); normalize(); }
}

theorem keeps_rewritten_concatenation(a: int32, b: int32) {
    requires a == b;
    ensures forall (unused: Integer) {
        [a] ++ [] == [b]
    } by { intro(); rewrite(a, b); normalize(); }
}

theorem sequence_premise_exposes_elements(a: int32, b: int32, c: int32, d: int32) {
    requires [a] ++ [b] == [c, d];
    ensures b == d by known();
}

theorem known_checks_each_element(a: int32, b: int32, c: int32, d: int32) {
    requires a == c;
    requires b == d;
    ensures [a, b] == [c] ++ [d] by known();
}

theorem all_checks_each_element(a: int32, b: int32, c: int32, d: int32) {
    requires a == c;
    requires b == d;
    ensures [a, b] == [c] ++ [d] by {
        all { a == c => { known(); } b == d => { known(); } }
    }
}

theorem wrong_length(a: int32) {
    ensures [a] ++ [] != [a, a] by normalize();
}

theorem wrong_element(a: int32, b: int32) {
    requires a != b;
    ensures [a] ++ [] != [b] by known();
}
```

```expect
pass
```
