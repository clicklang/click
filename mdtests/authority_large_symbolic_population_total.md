# A large symbolic birth publishes a nonnegative exact count

The first birth from the original overflow regression is admitted independently.
The caller retains the complete batch under authority; this does not assert
support for a second symbolic birth or for splitting that batch.

```c filename=population_total.c
void mint_n(int32* o, int32 n) {}
void first_birth(int32* o, int32 k) { mint_n(o, k); }
```

```click resource_semantics=authority
resource tok(o: int32*) {}
verifying "population_total.c";
void mint_n(int32* o, int32 n) {
    owns authority(tok(o));
    requires 0 < n;
    requires defined(count(tok(o)) + n);
    produces n of tok(o);
    ensures count(tok(o)) == old(count(tok(o))) + n;
} by { fold(n of tok(o)); execute(); simp(); }
void first_birth(int32* o, int32 k) {
    owns authority(tok(o));
    requires count(tok(o)) == 0;
    requires k == 2000000000;
    produces k of tok(o);
    ensures count(tok(o)) == k;
    ensures 0 <= count(tok(o));
} by { execute(); simp(); }
```

```expect
pass
```
