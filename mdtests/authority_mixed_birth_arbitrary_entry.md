# A symbolic birth and a unit birth retain an arbitrary entry total

```c filename=population_symbolic_increment_bounded.c
void mint_n(int32* o, int32 n) {}
void increment(int32* o, int32 n) { mint_n(o, n); mint_n(o, 1); }
```

```click
authorized resource tok(o: int32*) {}
verifying "population_symbolic_increment_bounded.c";
void mint_n(int32* o, int32 n) {
    owns authority(tok(o));
    requires 0 < n;
    requires defined(count(tok(o)) + n);
    produces n of tok(o);
    ensures count(tok(o)) == old(count(tok(o))) + n;
} by { fold(n of tok(o)); execute(); simp(); }
void increment(int32* o, int32 n) {
    owns authority(tok(o));
    requires defined(count(tok(o)) + n);
    requires defined((count(tok(o)) + n) + 1);
    requires defined(n + 1);
    requires 0 < n;
    requires n < 2147483647;
    ensures count(tok(o)) == old(count(tok(o))) + (n + 1);
} by { execute(); simp(); }
```

```expect
pass
```
