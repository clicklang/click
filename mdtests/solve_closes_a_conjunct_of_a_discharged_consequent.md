# `solve` closes a conjunct of a discharged implication's consequent

The goal `c == 2` is one conjunct of the consequent of `a != 0 implies
(b == 1 and c == 2)`, and the antecedent `a != 0` is a precondition. The
implicit closer extracts the whole consequent, spelled as the precondition is
written, and the goal is then a proper conjunct of an available fact. The
implication is found by one probe of an index of consequent conjuncts, so no
fact is scanned.

```c filename=solve_closes_a_conjunct_of_a_discharged_consequent.c
int32 f(int32 a, int32 b, int32 c) {
    return c;
}
```

```click
verifying "solve_closes_a_conjunct_of_a_discharged_consequent.c";

int32 f(int32 a, int32 b, int32 c) {
    requires a != 0;
    requires a != 0 implies (b == 1 and c == 2);
    ensures result == 2;
}
```

```expect
pass
```

Without the antecedent the consequent is not available
([`solve_does_not_close_a_conjunct_of_an_undischarged_consequent.md`](solve_does_not_close_a_conjunct_of_an_undischarged_consequent.md)).
