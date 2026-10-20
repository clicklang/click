# Address arithmetic keeps its C meaning under Integer arithmetic

Under `arithmetic "integer";` a comparison that does arithmetic compares exact
Integers, except where an arithmetic operand is a pointer. An `address(p)` is
such an operand: adding a tag to an aligned address is pointer-word arithmetic,
the C operation a tagged-pointer proof reasons about, so the comparison keeps
its C meaning. `p` here is a theorem parameter, which the comparison sees only
through `address(p)`. The same theorem without the directive is
`pointer_tag_read_from_alignment.md`.

```click
arithmetic "integer";

theorem packed_parent(p: int32*, word: uint64) {
    requires aligned(p, 8);
    ensures ((word & 1) | address(p)) == address(p) + (((word & 1) | address(p)) & 1) by {
        have (((word & 1) | address(p)) & 1) == (word & 1) by {
            arithmetic() using { aligned(p, 8); };
        }
        rewrite((((word & 1) | address(p)) & 1) == (word & 1));
        arithmetic() using { aligned(p, 8); };
    }
}
```

```expect
pass
```
