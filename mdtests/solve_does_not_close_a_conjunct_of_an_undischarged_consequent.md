# `solve` does not close a conjunct of an undischarged consequent

The goal `c == 2` is one conjunct of the consequent of `a != 0 implies
(b == 1 and c == 2)`, but nothing says `a != 0`, so the consequent is not
available and the goal is refused
([`solve_closes_a_conjunct_of_a_discharged_consequent.md`](solve_closes_a_conjunct_of_a_discharged_consequent.md)
closes it once the antecedent holds).

```c filename=solve_does_not_close_a_conjunct_of_an_undischarged_consequent.c
int32 f(int32 a, int32 b, int32 c) {
    return c;
}
```

```click
verifying "solve_does_not_close_a_conjunct_of_an_undischarged_consequent.c";

int32 f(int32 a, int32 b, int32 c) {
    requires a != 0 implies (b == 1 and c == 2);
    ensures result == 2;
}
```

```expect
fail: `ensures result == 2` failed
```
