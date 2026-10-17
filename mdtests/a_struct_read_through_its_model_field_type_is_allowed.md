# A struct read through its model-field type is allowed

The control for
`a_struct_read_through_a_model_field_pointer_to_another_struct_is_refused.md`.
The model field's declared `struct a` class reaches the decoded pointer, and
`q->x` reads it through `struct a`. The resource carries the decoded C value
as a pointer argument so its bounds remain part of the relationship.

```c filename=model_alias.c
struct a { int32 x; };
struct b { int32 y; };
int32 read_b(uint64 w) {
    struct a* q = (struct a*)w;
    return q->x;
}
```
```click
verifying "model_alias.c";
spec enum Held { At(struct a*), }
resource held_a(w: uint64, decoded: struct a*) {
    field model: Held;
    match model { Held::At(q) => { owns q->x; fact w == address(q); fact decoded == q; }, }
}
int32 read_b(uint64 w) {
    owns h: held_a(w, (struct a*)w);
    ensures 1 == 1;
} by {
    match h.model { Held::At(obj) => {
        unfold(h);
        step();
        let h = fold(held_a(w, (struct a*)w), { model: Held::At(obj) });
        execute();
    } }
}
```
```expect
pass
```
