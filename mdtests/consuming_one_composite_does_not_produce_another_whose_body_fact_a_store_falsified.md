# Consuming one composite does not produce another whose body fact a store falsified

`mk` consumes `zt(p)` and produces `zt2(p)`, a second resource with the same
body. After its C store, `p[5] == 0` is false, so the exit cannot assemble
`zt2(p)` from the bytes `zt(p)` gave it; otherwise `use` proves
`result == 0` of a function returning 9.

```c filename=exchange_produces_unchecked_composite.c
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

resource zt2(p: uint8*) {
    owns p[0..6];
    fact p[5] == 0;
}

verifying "exchange_produces_unchecked_composite.c";

void mk(uint8* p) {
    consumes zt(p);
    produces zt2(p);
} by {
    unfold(zt(p));
    execute();
}

uint8 use(uint8* p) {
    consumes zt(p);
    produces zt2(p);
    ensures result == 0;
} by {
    step();
    unfold(zt2(p));
    execute();
    simp();
}
```

```expect
fail: Requires produces zt2(p)
```
