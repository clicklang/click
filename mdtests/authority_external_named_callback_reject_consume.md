# Named callback contracts retain authority semantics at their entry boundary

```c filename=callback.c
void invoke(void (*callback)(int32*), int32* pool) { callback(pool); }
```

```click
authorized resource token(pool: int32*) {}
contract void Keep(int32* pool) {
    owns authority(token(pool));
    consumes token(pool);
    ensures count(token(pool)) == old(count(token(pool))) - 1;
}
verifying "callback.c";
void invoke(void (*callback)(int32*), int32* pool) {
    requires Keep(callback);
    owns authority(token(pool));
    owns token(pool);
    ensures count(token(pool)) == old(count(token(pool)));
} by { step(Keep); execute(); simp(); }
```

```expect
fail: its assumed contract changes a population or mutex resource
```
