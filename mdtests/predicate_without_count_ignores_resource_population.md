# ordinary predicate identity ignores resource populations

A predicate that does not observe `count(...)` depends only on its explicit
arguments. Folding a composite resource may update Click's ghost population
ledger, but that unrelated transition must not change the identity of an
already-proved memory predicate needed by the resource body.

The helper receives authority for an empty family explicitly and exchanges its
owned cell for the first member. Its count-independent predicate still holds
after that checked birth.

```c filename=predicate_without_count_ignores_resource_population.c
void wrap_zero(int32 *cell) {
}
```

```click
predicate is_zero(cell: int32*) {
    cell[0] == 0
}

authorized resource zero_cell(cell: int32*) {
    owns cell[0..1];
    fact is_zero(cell);
}

verifying "predicate_without_count_ignores_resource_population.c";

void wrap_zero(int32* cell) {
    requires is_zero(cell);
    owns authority(zero_cell(cell));
    requires count(zero_cell(cell)) == 0;
    consumes cell[0..1];
    produces zero_cell(cell);
} by {
    unfold(is_zero);
    fold(zero_cell(cell));
    execute();
    simp();
}
```

```expect
pass
```
