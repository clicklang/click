# An ordinary exit produces a composite whose body facts hold

The twin of
`an_ordinary_exit_does_not_produce_a_composite_whose_body_fact_a_store_falsified.md`:
the C store now makes the body fact `p[5] == 0` true. `mk` folds `zt(p)`
explicitly; `mk_at_exit` leaves the fold to its ordinary exit, which
assembles `zt(p)` from the owned bytes because the fact holds there; `mk_from`
establishes the fact from its precondition rather than a constant store. `use` unfolds the produced instance and reads the fact.

```c filename=exit_produces_checked_composite.c
void mk(unsigned char *p)
{
	p[5] = 0;
}

void mk_at_exit(unsigned char *p)
{
	p[5] = 0;
}

void mk_from(unsigned char *p, unsigned char v)
{
	p[5] = v;
}

unsigned char use(unsigned char *p)
{
	mk(p);
	return p[5];
}
```

```click
resource zt(p: uint8*) {
    owns p[0..6];
    fact p[5] == 0;
}

verifying "exit_produces_checked_composite.c";

void mk(uint8* p) {
    consumes p[0..6];
    produces zt(p);
} by {
    execute();
    fold(zt(p));
}

void mk_at_exit(uint8* p) {
    consumes p[0..6];
    produces zt(p);
} by {
    execute();
}

void mk_from(uint8* p, uint8 v) {
    requires v == 0;
    consumes p[0..6];
    produces zt(p);
} by {
    execute();
}

uint8 use(uint8* p) {
    owns p[0..6];
    ensures result == 0;
} by {
    step();
    unfold(zt(p));
    execute();
    simp();
}
```

```expect
pass
```
