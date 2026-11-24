# `load<Pointer>` reads a typed pointer field's value

Click's untyped pointer `Pointer` is an address and a provenance with no
pointee type (`design/pointer-model.md`, "Types belong to terms, not
values"). `load<Pointer>(&s->next)` reads the eight-byte cell of an `int32 *`
field. Its value is the field's pointer, so value equality with the typed
read holds, and a cast back to `int32 *` keeps that value.

```c filename=untyped_pointer_field.c
struct node {
    int32 *next;
    int32 v;
};

int32 *next_of(struct node *s) {
    return s->next;
}
```

```click
verifying "untyped_pointer_field.c";

int32 *next_of(struct node *s) {
    views s->next;
    ensures load<Pointer>(&s->next) == s->next;
    ensures result == load<Pointer>(&s->next) as (int32 *);
}
```

```expect
pass
```
