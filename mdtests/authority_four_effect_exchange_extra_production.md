# A four-effect helper cannot hide an extra slot birth

The helper promises one source slot but creates two. The population transition
must reject this discrepancy even without explicit count postconditions.

```c filename=four_effect_exchange.c
void move(int32* source, int32* destination, int32* p) {}

```

```click
authorized resource slot(pool: int32*) {}
authorized resource item(pool: int32*, p: int32*) { owns p[0..1]; }
verifying "four_effect_exchange.c";
void move(int32* source, int32* destination, int32* p) {
    requires source != destination;
    owns authority(slot(source));
    owns authority(slot(destination));
    owns authority(item(source, _));
    owns authority(item(destination, _));
    consumes item(source, p);
    consumes slot(destination);
    requires defined(count(slot(source)) + 1);
    requires defined(count(item(destination, _)) + 1);
    produces item(destination, p);
    produces slot(source);
    ensures p[0] == old(p[0]);
} by {
    unfold(item(source, p));
    unfold(slot(destination));
    fold(item(destination, p));
    fold(slot(source)); fold(slot(source));
    execute(); simp();
}

```

```expect
fail: Requires produces slot(source)
```
