# Exactly known batches transfer and spend independently

The caller retains one billion members while a helper consumes the other
billion. The quantity is spelled symbolically and pinned by an exact fact.

```c filename=exact_batches.c
void mint_n(int32* o, int32 n) {}
void spend_n(int32* o, int32 n) {}
void run(int32* o, int32 k) {
    mint_n(o, k);
    mint_n(o, k);
    spend_n(o, k);
}
```

```click resource_semantics=authority
resource tok(o: int32*) {}
verifying "exact_batches.c";
void mint_n(int32* o, int32 n) {
    owns authority(tok(o));
    requires 0 < n;
    requires defined(count(tok(o)) + n);
    produces n of tok(o);
    ensures count(tok(o)) == old(count(tok(o))) + n;
} by { fold(n of tok(o)); execute(); simp(); }
void spend_n(int32* o, int32 n) {
    owns authority(tok(o));
    requires 0 < n;
    consumes n of tok(o);
    ensures count(tok(o)) == old(count(tok(o))) - n;
} by { unfold(n of tok(o)); execute(); simp(); }
void run(int32* o, int32 k) {
    owns authority(tok(o));
    requires count(tok(o)) == 0;
    requires k == 1000000000;
    produces k of tok(o);
    ensures count(tok(o)) == k;
} by { execute(); simp(); }
```

```expect
pass
```
