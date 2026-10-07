# A transfer keyed on arguments that may alias a tracked population is refused

`run` observes the `ticket` family through its postcondition (a tautology,
kept only so that the family is observed and the entry ledger tracks
`ticket(p)` and `ticket(q)` as two populations with symbolic counts).
`spend(p)` transfers one unit keyed on `p`; nothing relates `p` and `q`, so the
transfer may be spending a unit of the population tracked under `q`. The
transfer is refused at the call, naming both keys and the open argument
position, rather than updating one entry and leaving the other's count stale.
Before the fix this file verified.

```c filename=population_transfer_may_alias_tracked_population_rejected.c
void spend(void *argument) { }
int run(void *p, void *q) {
    spend(p);
    spend(q);
    return 1;
}
```

```click
verifying "population_transfer_may_alias_tracked_population_rejected.c";
abstract resource ticket(p: void*);
void spend(void* argument) {
    consumes ticket(argument);
} by { execute(); simp(); }
int32 run(void* p, void* q) {
    consumes ticket(p);
    consumes ticket(q);
    ensures count(ticket(p)) == count(ticket(p));
} by {
    execute();
    simp();
}
```

```expect
fail: population transfer of `ticket(...)` may alias the tracked population `ticket(...)`
```
