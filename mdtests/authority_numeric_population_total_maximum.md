# Numeric births can reach the exact population limit

```c filename=population_total.c
void mint_n(int32* o, int32 n) {}
void total(int32* o) { mint_n(o, 1000000000); mint_n(o, 1147483647); }
```

```click
authorized resource tok(o: int32*) {}
verifying "population_total.c";
void mint_n(int32* o, int32 n) {
    owns authority(tok(o));
    requires 0 < n;
    requires defined(count(tok(o)) + n);
    produces n of tok(o);
    ensures count(tok(o)) == old(count(tok(o))) + n;
} by { fold(n of tok(o)); execute(); simp(); }
void total(int32* o) {
    owns authority(tok(o));
    requires count(tok(o)) == 0;
    produces 1000000000 of tok(o);
    produces 1147483647 of tok(o);
    ensures count(tok(o)) == 2147483647;
} by { execute(); simp(); }
```

```expect
pass
```
