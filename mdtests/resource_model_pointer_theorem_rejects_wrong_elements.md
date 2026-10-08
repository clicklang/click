# Pointer capture keeps incompatible element types distinct

A declared word pointer cannot acquire byte-pointer type from the theorem's
parameter.

```c filename=simple.c
void keep(const uint32* p, int32 i) {}
```

```click
verifying "simple.c";
spec enum Link { Node(const uint32*) }
resource Cell(p: const uint32*, i: int32) {
 field model: Link;
 match model { Link::Node(q) => { owns p[0..i + 4]; fact q == p; }, }
}
theorem bounded_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 22200;
 ensures (base + index) + 4 == base + (index + 4) by {
  have defined(index + 4) by { simp() using { 0 <= index; index <= 22200; } }
  normalize() using { defined(index + 4); }
 }
}
void keep(const uint32* p, int32 i) {
 requires 0 <= i;
 requires i <= 22200;
 owns h: Cell(p, i);
} by {
 match h.model {
  Link::Node(q) => {
   unfold(h);
   have defined(i + 4) by { simp() using { 0 <= i; i <= 22200; } }
   have (q + i) + 4 == q + (i + 4) by { apply(bounded_pointer_association(q, i)) using { 0 <= i; i <= 22200; } }
   have ((q + 1) + i) + 4 == (q + 1) + (i + 4) by { apply(bounded_pointer_association(q + 1, i)) using { 0 <= i; i <= 22200; } }
   have (old(q) + i) + 4 == old(q) + (i + 4) by { apply(bounded_pointer_association(old(q), i)) using { 0 <= i; i <= 22200; } }
   mark model_ready;
   have (at(model_ready, q) + i) + 4 == at(model_ready, q) + (i + 4) by { apply(bounded_pointer_association(at(model_ready, q), i)) using { 0 <= i; i <= 22200; } }
   let h = fold(Cell(p, i), { model: Link::Node(q) });
   execute(); simp();
  },
 }
}

```

```expect
fail: expects UInt8 array elements, got UInt32
```
