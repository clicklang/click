# Spending members of two distinct populations counts each separately

`run` holds the authority for `ticket(p)` and for `ticket(q)`, which are
distinct, and spends one member of each through `spend`. Only the `ticket(p)`
population loses the member spent from it.

```c filename=authority_population_count_distinct_arguments_consumption.c
void spend(void *argument) { }
int run(void *p, void *q) {
    spend(p);
    spend(q);
    return 1;
}
```

```click
verifying "authority_population_count_distinct_arguments_consumption.c";
authorized resource ticket(p: void*) {}
void spend(void* argument) {
    owns authority(ticket(argument));
    consumes ticket(argument);
    ensures count(ticket(argument)) == old(count(ticket(argument))) - 1;
} by {
    unfold(ticket(argument));
    execute();
    simp();
}
int32 run(void* p, void* q) {
    owns authority(ticket(p));
    owns authority(ticket(q));
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
