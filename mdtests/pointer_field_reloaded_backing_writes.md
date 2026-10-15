# Repeated writes through a reloaded backing pointer

```c filename=probe.c
struct owner { int32 len; int32 cap; int32* data; };
int32 probe(struct owner* owner, int32 index, int32 value) {
    owner->data[0] = value;
    owner->data[1] = 0;
    return value;
}
```

```click
verifying "probe.c";
resource buffer(owner: struct owner*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}
int32 probe(struct owner* owner, int32 index, int32 value) {
    requires 0 <= index;
    requires index < owner->len;
    requires 2 <= owner->cap;
    owns buffer(owner);
    ensures result == value;
    ensures owner->data[0] == value;
} by {
    unfold(buffer(owner));
    step();
    step();
    have separate(memory(*owner), memory(owner->data[0..owner->cap])) by { simp(); }
    have owner->data[0] == value by { simp(); }
    fold(buffer(owner));
    step();
    assumption();
    assumption();
    assumption();
}
```

```expect
pass
```
