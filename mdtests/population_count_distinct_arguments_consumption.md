# Distinct population keys are counted and transferred independently

With `p != q` established, `ticket(p)` and `ticket(q)` are two populations:
`count(ticket(p))` totals the one entry, and spending a unit of `ticket(q)`
leaves it untouched. This is the passing twin of
`population_count_alias_consumption_rejected.md`.

```c filename=population_count_distinct_arguments_consumption.c
void spend(void *argument) { }
int run(void *p, void *q) {
    spend(p);
    spend(q);
    return 1;
}
```

```click
verifying "population_count_distinct_arguments_consumption.c";
abstract resource ticket(p: void*);
void spend(void* argument) {
    consumes ticket(argument);
} by { execute(); simp(); }
int32 run(void* p, void* q) {
    consumes ticket(p);
    consumes ticket(q);
    requires p != q;
    requires count(ticket(p)) == 2;
    ensures count(ticket(p)) == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
