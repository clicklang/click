# A four-effect helper must consume its second declared member

The helper transfers the object and creates the source slot, but leaves its
second declared input unconsumed. Returning a borrowed authority cannot hide
that missing transition, even when the contract states no count postcondition.

```c filename=four_effect_exchange.c
void move(int32* source, int32* destination, int32* p) {}

```

```click resource_semantics=authority
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
    fold(item(destination, p));
    fold(slot(source));
    execute(); simp();
}

```

```expect
fail: Requires consumes slot(destination)
```
