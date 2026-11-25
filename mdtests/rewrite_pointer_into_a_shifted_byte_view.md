# Rewrite a pointer into a shifted byte view

The proof restricts the owned range to `p[i..i + 4]`, rebases it with
`contains_rebase`, then selects the literal four-byte interval with
`contains_subrange`. Each containment carries viewability through
`viewable_restrict`, using explicit bounds and the pointer equality.

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
            fact to_integer(i) <= to_integer(i + 4);
            fact to_integer(i + 4) <= to_integer(n);
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
            have contains(memory(p[0..n]), memory(p[i..i + 4])) by {
                apply(click::separation::contains_subrange(p, 0, n, i, i + 4));
            }
            have viewable(p[i..i + 4]) by {
                apply(click::separation::viewable_restrict(memory(p[0..n]), memory(p[i..i + 4])));
            }
            have viewable(q[0..4]) by {
                rewrite(q, p + i);
                have contains(memory(p[i..i + 4]), memory((p + i)[0..(i + 4) - i])) by {
                    apply(click::separation::contains_rebase(p, i, i + 4));
                }
                have viewable((p + i)[0..(i + 4) - i]) by {
                    apply(click::separation::viewable_restrict(memory(p[i..i + 4]), memory((p + i)[0..(i + 4) - i])));
                }
                have 0 <= 0 by { close(); }
                have 0 <= 4 by { close(); }
                have to_integer(4) <= to_integer((i + 4) - i) by {
                    apply(click::integer::int32_add_to_integer(i, 4));
                    apply(click::integer::int32_subtract_to_integer(i + 4, i));
                    rewrite(to_integer((i + 4) - (i)), to_integer(i + 4) - to_integer(i));
                    rewrite(to_integer(i + 4), to_integer(i) + 4);
                    close();
                }
                have contains(memory((p + i)[0..(i + 4) - i]), memory((p + i)[0..4])) by {
                    apply(click::separation::contains_subrange(p + i, 0, (i + 4) - i, 0, 4));
                }
                apply(click::separation::viewable_restrict(memory((p + i)[0..(i + 4) - i]), memory((p + i)[0..4])));
            }
            let h = fold(Cell(p, n, i), { model: Link::Node(q) });
            step_until(function.exit);
            close();
        },
    }
}
```

```expect
pass
```
