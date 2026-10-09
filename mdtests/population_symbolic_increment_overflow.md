# A symbolic population increment overflow

```c filename=population_symbolic_increment_overflow.c
void mint_n(int32* o, int32 n) {}
void increment(int32* o, int32 n) { mint_n(o, n); mint_n(o, 1); }
```

```click
authorized resource tok(o: int32*) {}
verifying "population_symbolic_increment_overflow.c";
void mint_n(int32* o, int32 n) {
    owns authority(tok(o));
    requires 0 < n;
    requires defined(count(tok(o)) + n);
    produces n of tok(o);
    ensures count(tok(o)) == old(count(tok(o))) + n;
} by { fold(n of tok(o)); execute(); simp(); }
void increment(int32* o, int32 n) {
    owns authority(tok(o));
    requires count(tok(o)) == 0;
    requires n == 2147483647;
    ensures count(tok(o)) < 0;
} by { execute(); simp(); }
```

```expect
fail: PopulationCountOverflow
```
