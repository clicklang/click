# Exact symbolic quantities compose as numeric batches

All original C is retained. The caller proves an exact numeric value for `k`,
then births two separately accounted batches with their mathematical total.

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

```click resource_semantics=authority
resource tok(o: int32*) {
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
    requires k == 1000000000;
    produces k of tok(o);
    produces k of tok(o);

    ensures count(tok(o)) == 2000000000;
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
pass
```
