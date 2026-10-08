# A pointer alias supplies no extra byte

The cited shifted view covers four bytes. Equality of the pointers does not
turn it into a five-byte view.

```c filename=alias.c
void keep(const uint8* p, int32 n, int32 i) {}
```

```click
verifying "alias.c";

spec enum Link { Node(const uint8*) }
resource Cell(p: const uint8*, n: int32, i: int32) {
    field model: Link;
    match model {
        Link::Node(q) => {
            owns p[0..n];
            fact 0 <= i;
            fact i <= i + 4;
            fact i + 4 <= n;
            fact q == p + i;
        },
    }
}

void keep(const uint8* p, int32 n, int32 i) {
    requires 0 <= n;
    requires n <= 22204;
    requires 0 <= i;
    requires i <= 22200;
    owns h: Cell(p, n, i);
} by {
    match h.model {
        Link::Node(q) => {
            unfold(h);
            have viewable(p[i..i + 4]) by {
                transport(viewable(p[0..n]), viewable(p[i..i + 4])) using {
                    viewable(p[0..n]);
                    0 <= i;
                    i <= i + 4;
                    i + 4 <= n;
                }
            }
            have viewable(q[0..5]) by {
                rewrite(q == p + i);
                simp() using { viewable(p[i..i + 4]); }
            }
            let h = fold(Cell(p, n, i), { model: Link::Node(q) });
            execute();
            simp();
        },
    }
}
```

```expect
fail: `simp() using` could not prove the current goal from only its listed premises
```
