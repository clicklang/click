# Spending a possibly aliased member needs that member's own authority

`run` holds the authority for `ticket(p)` only, plus one member of
`ticket(p)` and one of `ticket(q)`, with nothing known about `p` and `q`.
A count comes from the authority's ledger, not from the owned entries a key
happens to spell, so an aliased total is never ambiguous. Spending the `ticket(q)` member needs
`authority(ticket(q))`, which `run` does not hold, so the second call is
refused.

```c filename=authority_population_count_alias_spend_requires_authority.c
void spend(void *argument) { }
int run(void *p, void *q) {
    spend(p);
    spend(q);
    return 1;
}
```

```click
verifying "authority_population_count_alias_spend_requires_authority.c";
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
fail: Requires owns authority(ticket(...))
```
