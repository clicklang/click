# A count over a population that may alias another is refused

`run` owns one unit of `ticket(p)` and one of `ticket(q)` and states nothing
about `p` and `q`. When `p == q` both units belong to one population, so
`count(ticket(p))` is the total of both ledger entries; when `p != q` it is one
entry's count. The facts determine neither, so the observation has no value
and is refused where it is written, instead of totalling only the entry whose
key is spelled `p` and certifying `count(ticket(p)) == 1` after both units are
spent (`bugs/population-count-ignores-possibly-aliased-arguments.md`).

```c filename=population_count_alias_consumption_rejected.c
void spend(void *argument) { }
int run(void *p, void *q) {
    spend(p);
    spend(q);
    return 1;
}
```

```click
verifying "population_count_alias_consumption_rejected.c";
abstract resource ticket(p: void*);
void spend(void* argument) {
    consumes ticket(argument);
} by { execute(); simp(); }
int32 run(void* p, void* q) {
    consumes ticket(p);
    consumes ticket(q);
    requires count(ticket(p)) == 2;
    ensures count(ticket(p)) == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: may alias
```
