# a population count is not a wrapped total

A population count is a mathematical natural number. Two `produces k of
tok(o)` clauses at `k == 2000000000` are four billion units, and composing
them with the modular add made them a population of `-294967296` — so
`ensures count(tok(o)) < 0` verified of a function that had just produced
them. Authority keeps the population separate from member custody. The first birth
produces two billion members; the second is rejected by the checked member-transition boundary, so no
wrapped negative count is published. Repeated symbolic births remain
unsupported even for bounded totals; this fixture does not claim otherwise.

`counts_a_total_it_can_state` beside it is the other polarity: constant
quantities whose sum is a count are still added, and the count is that sum.

The call transition refuses the overflowing population before publishing a
post-count, at the second call. Its required addition domain also cannot hold.
`authority_large_symbolic_population_total.md` proves that the first birth is
admitted, while `authority_numeric_population_total.md` verifies the original
numeric caller independently.

```c filename=a_population_count_is_not_a_wrapped_total.c
void mint_n(int32* o, int32 n) {
}

void wraps_its_population(int32* o, int32 k) {
    mint_n(o, k);
    mint_n(o, k);
}

void counts_a_total_it_can_state(int32* o) {
    mint_n(o, 3);
    mint_n(o, 4);
}
```

```click
authorized resource tok(o: int32*) {
}

verifying "a_population_count_is_not_a_wrapped_total.c";

void mint_n(int32* o, int32 n) {
    owns authority(tok(o));
    requires 0 < n;
    requires defined(count(tok(o)) + n);
    produces n of tok(o);
    ensures count(tok(o)) == old(count(tok(o))) + n;
} by {
    fold(n of tok(o));
    execute();
    simp();
}

void wraps_its_population(int32* o, int32 k) {
    owns authority(tok(o));
    requires count(tok(o)) == 0;
    requires k == 2000000000;
    produces k of tok(o);
    produces k of tok(o);

    ensures count(tok(o)) < 0;
} by {
    execute();
    simp();
}

void counts_a_total_it_can_state(int32* o) {
    owns authority(tok(o));
    requires count(tok(o)) == 0;
    produces 3 of tok(o);
    produces 4 of tok(o);

    ensures count(tok(o)) == 7;
} by {
    execute();
    simp();
}
```

```expect
fail: population helper member transition refused
```
