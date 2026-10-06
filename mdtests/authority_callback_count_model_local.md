# Alternative callback guarantees cannot read the selected population model

The scalar control retains its original C separately. This population companion
keeps explicit authorities and an exact-one entry bound while selecting Keep;
Alternative's resource transition must not supply a result guarantee from Keep's
unchanged A population.

```c filename=callback_model.c
int32 invoke(int32 (*callback)(int32*), int32* pool) { return callback(pool); }
```

```click resource_semantics=authority
resource A(pool: int32*) {}
resource B(pool: int32*) {}
contract int32 Keep(int32* pool) {
    owns authority(A(pool));
    owns authority(B(pool));
    owns A(pool);
    requires count(A(pool)) == 1;
    ensures result == 0;
}
contract int32 Alternative(int32* pool) {
    owns authority(A(pool));
    owns authority(B(pool));
    consumes A(pool);
    produces B(pool);
    requires count(A(pool)) == 1;
    ensures count(A(pool)) == 1 implies result == 1;
}
verifying "callback_model.c";
int32 invoke(int32 (*callback)(int32*), int32* pool) {
    requires Keep(callback);
    requires Alternative(callback);
    owns authority(A(pool));
    owns authority(B(pool));
    owns A(pool);
    requires count(A(pool)) == 1;
    ensures result == 1;
} by { step(Keep); execute(); simp(); }
```

```expect
fail: unclosed goal
```
