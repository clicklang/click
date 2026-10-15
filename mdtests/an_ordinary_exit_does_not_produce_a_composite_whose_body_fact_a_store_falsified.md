# An ordinary exit does not produce a composite whose body fact a store falsified

`mk` consumes the six bytes and produces `zt(p)`, whose body asserts
`p[5] == 0`, but its C store makes `p[5]` nine and the proof never folds.
The exit may assemble `zt(p)` from the owned bytes only when every body fact
holds there, as an explicit `fold(zt(p))` requires; otherwise `use` would
unfold the false fact and prove `result == 0` of a function returning 9.

```c filename=exit_produces_unchecked_composite.c
void mk(unsigned char *p)
{
	p[5] = 9;
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

verifying "exit_produces_unchecked_composite.c";

void mk(uint8* p) {
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
fail: Requires produces zt(p)
```
