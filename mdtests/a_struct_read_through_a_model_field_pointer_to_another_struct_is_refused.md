# A struct read through a model-field pointer to another struct is refused

The model field is declared `struct a*`, so the object it designates has the
class `struct a`, as a `struct a*` parameter's object does. Its address is
passed as an integer and decoded as a `struct b*`. The decoded pointer keeps
the original class, so `q->y` is a `struct b` access to a `struct a` and is
refused (C11 6.5p7). Before model fields carried a class, the decoded pointer
had none and the read was accepted. The same read through `struct a`
verifies (`a_struct_read_through_its_model_field_type_is_allowed.md`). The
resource carries the full decoded pointer alongside its numeric word key.

```c filename=model_alias.c
struct a { int32 x; };
struct b { int32 y; };
int32 read_b(uint64 w) {
    struct b* q = (struct b*)w;
    return q->y;
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
fail: an object of type `struct a` accessed through an lvalue of type `struct b`
```
