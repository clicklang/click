# Separate member clauses for one population are one entry custody

A helper that keeps one member with `owns` and consumes two more holds three
members of the population at entry, so it can spend two of them and return
the third.

```c filename=authority_entry_separate_member_clauses.c
int run(void *p) { return 0; }
```

```click resource_semantics=authority
verifying "authority_entry_separate_member_clauses.c";
authorized resource ticket(p: void*) {}
int32 run(void* p) {
    owns authority(ticket(p));
    owns ticket(p);
    consumes 2 of ticket(p);
    requires count(ticket(p)) == 3;
    ensures result == 0;
} by {
    unfold(ticket(p));
    unfold(ticket(p));
    have count(ticket(p)) == 1;
    step();
    simp();
}
```

```expect
pass
```
