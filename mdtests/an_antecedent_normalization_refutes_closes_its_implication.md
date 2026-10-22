# An antecedent normalization refutes closes its implication

Specification arithmetic is Integer arithmetic, so `i == i + 1` is the Integer
comparison `to_integer(i) == to_integer(i) + 1`. `normalize()` decides it
false from the goal alone: every term cancels and the constants differ.

Two closers rely on that decision. `contradiction(P)` accepts a held `P`
whose negation normalizes to true; the negation of a condition is the same
condition at the other polarity, which is the form `normalize()` decides, so
`contradiction(to_integer(i) + 1 == to_integer(i))` closes the branch.

`simp` and `auto` introduce an implication whose antecedent normalization
refutes and close it by that `contradiction`, reading only the goal. A loop
invariant such as `i == at(loop(0).entry, i) + 1 implies n <= 5u64` has this
shape at the loop's entry, where `i` is its entry value; the consequent
mentions `n`, which no fact about `i` reaches.

```c filename=refuted_antecedent.c
int r(int i, unsigned long n) { return i; }
```

```click
verifying "refuted_antecedent.c";

int32 r(int32 i, uint64 n) {
    requires 0 <= i and i < 4;
    ensures true;
} by {
    have to_integer(i) + 1 == to_integer(i) implies n <= 5u64 by {
        intro();
        contradiction(to_integer(i) + 1 == to_integer(i));
    }
    have i == i + 1 implies n <= 5u64 by { simp(); }
    have i <= i + 4 implies i == i + 1 implies n <= 5u64 by { auto(); }
    execute();
    simp();
}
```

```expect
pass
```
