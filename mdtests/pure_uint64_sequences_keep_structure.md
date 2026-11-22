# Pure uint64 sequences retain equality, membership and concatenation

```click
theorem wide_sequence_equality(a: uint64, b: uint64) {
    ensures forall (unused: Integer) {
        [] ++ [a] ++ [b] == [a, b] ++ []
    } by { intro(); known(); }
}

theorem wide_literal_membership() {
    ensures forall (unused: Integer) {
        18446744073709551615u64 in [] ++ [0u64, 18446744073709551615u64]
    } by { intro(); known(); }
}

theorem wide_empty_membership(a: uint64) {
    ensures forall (unused: Integer) {
        not (a in [])
    } by { intro(); known(); }
}

theorem wide_rewritten_membership(a: uint64, b: uint64) {
    requires a == b;
    ensures a in [] ++ [b] by { rewrite(a, b); known(); }
}

theorem wide_rewritten_equality(a: uint64, b: uint64) {
    requires a == b;
    ensures [a] ++ [] == [b] by { rewrite(a, b); known(); }
}

theorem wide_sequence_disequality(a: uint64) {
    ensures [a] != [a, a] by { known(); }
}

theorem wide_sequence_supplies_element_equalities(a: uint64, b: uint64, c: uint64, d: uint64) {
    requires [a] ++ [c] == [b, d];
    ensures a == b by { known(); }
}

theorem wide_cases_over_membership(a: uint64) {
    requires a in [1u64] ++ [2u64];
    ensures 0u64 < a by {
        cases { a == 1u64 => { solve(); } a == 2u64 => { solve(); } }
    }
}
```

```expect
pass
```
