# A helper combines two symbolic births and returns their complete batch

The quantities remain symbolic. The helper checks both count additions and
returns one batch; a caller receives that same batch through the checked call
engine. No exact numeric value or global-total inference supplies custody.

```c filename=symbolic_birth_composition.c
void mint_pair(int32* o, int32 n, int32 m) {}
void run(int32* o, int32 n, int32 m) { mint_pair(o, n, m); }
```

```click resource_semantics=authority
resource tok(o: int32*) {}
verifying "symbolic_birth_composition.c";
void mint_pair(int32* o, int32 n, int32 m) {
    owns authority(tok(o));
    requires count(tok(o)) == 0;
    requires 0 < n;
    requires 0 < m;
    requires defined(n + m);
    requires 0 <= n + m;
    produces (n + m) of tok(o);
    ensures count(tok(o)) == n + m;
} by {
    fold(n of tok(o));
    have count(tok(o)) == n by simp;
    have defined(count(tok(o)) + m) by {
        rewrite(count(tok(o)) == n);
        simp();
    }
    fold(m of tok(o));
    execute(); simp();
}
void run(int32* o, int32 n, int32 m) {
    owns authority(tok(o));
    requires count(tok(o)) == 0;
    requires 0 < n;
    requires 0 < m;
    requires defined(n + m);
    requires 0 <= n + m;
    produces (n + m) of tok(o);
    ensures count(tok(o)) == n + m;
} by { execute(); simp(); }
```

```expect
pass
```
