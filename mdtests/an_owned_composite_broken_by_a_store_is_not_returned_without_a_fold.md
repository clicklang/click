# An owned composite broken by a store is not returned without a fold

`mk` borrows `zt(p)` under `owns`, unfolds it, and its C store falsifies the
body fact `p[5] == 0`. Returning the instance is a fold of the bytes it now
owns, so it needs that fact; the ordinary exit must not hand `zt(p)` back,
or `use` proves `result == 0` of a function returning 9.

```c filename=owns_returns_unchecked_composite.c
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

verifying "owns_returns_unchecked_composite.c";

void mk(uint8* p) {
    owns zt(p);
} by {
    unfold(zt(p));
    execute();
}

uint8 use(uint8* p) {
    owns zt(p);
    ensures result == 0;
} by {
    step();
    unfold(zt(p));
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns zt(p)`
```
