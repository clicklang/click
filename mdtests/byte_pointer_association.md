# Associate bounded byte pointer offsets

A pointer displacement adds exact bytes. Regrouping it into a signed index
requires checked addition definedness; the certificate cites that guard only.

```c filename=simple.c
void keep(const uint8* p, int32 i) {}
```

```click
verifying "simple.c";
spec enum Link { Node(const uint8*) }
resource Cell(p: const uint8*, i: int32) {
 field model: Link;
 match model { Link::Node(q) => { owns p[0..i + 4]; fact q == p; }, }
}
void keep(const uint8* p, int32 i) {
 requires 0 <= i;
 requires i <= 22200;
 owns h: Cell(p, i);
} by {
 match h.model {
  Link::Node(q) => {
   unfold(h);
   have defined(i + 4) by { simp() using { 0 <= i; i <= 22200; } }
   have (q + i) + 4 == q + (i + 4) by { normalize() using { defined(i + 4); } }
   let h = fold(Cell(p, i), { model: Link::Node(q) });
   execute(); simp();
  },
 }
}

```

```expect
pass
```
