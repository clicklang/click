# Unfolded separation retains physical range identity

A call can retain carrier ancestry separately from the address used to spell a
resource body. Restating its separation fact uses the same physical ranges;
`assumption` must find that fact without searching other facts or read history.

```c filename=probe.c
struct arena { int *data; int *occupied; int capacity; };
void idle(struct arena *arena) {}
void probe(struct arena *arena) { idle(arena); }
```

```click
verifying "probe.c";
resource state(arena: struct arena*) {
    field capacity: int32;
    owns *arena;
    fact 0 <= arena->capacity;
    fact arena->capacity <= 536870911;
    fact arena->capacity == capacity;
    fact separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data[0..arena->capacity]));
}
void idle(struct arena* arena) { owns st: state(arena); }
void probe(struct arena* arena) { owns st: state(arena); } by {
    step(idle, { st: st });
    let { capacity: cap } = unfold(st);
    have separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data[0..arena->capacity])) by { assumption(); }
    let st = fold(state(arena), { capacity: cap });
    step();
    assumption();
}
```

```expect
pass
```
