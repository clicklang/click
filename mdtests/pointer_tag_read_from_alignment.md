# Read the low tag bits of an aligned pointer word

Constructing a tagged address and reading its tag use the same checked alignment.
This catches the missing certificate case for reading low bits, including a
wrapped unsigned sum with an unrestricted tag and a mask smaller than the tag.

```click
theorem read_tag(p: int32*, word: uint64) {
    requires aligned(p, 8);
    ensures (((word & 7) | address(p)) & 3) == (word & 3) by {
        arithmetic() using { aligned(p, 8); }
    }
    ensures (word & 7) == ((address(p) + word) & 7) by {
        arithmetic() using { aligned(p, 8); }
    }
}

theorem packed_parent(p: int32*, word: uint64) {
    requires aligned(p, 8);
    ensures ((word & 1) | address(p)) == address(p) + (((word & 1) | address(p)) & 1) by {
        have (((word & 1) | address(p)) & 1) == (word & 1) by {
            arithmetic() using { aligned(p, 8); }
        }
        rewrite((((word & 1) | address(p)) & 1) == (word & 1));
        arithmetic() using { aligned(p, 8); }
    }
}
```

```expect
pass
```
