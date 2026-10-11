# Exact index observations connect native and signed byte addresses

Both widths remain intact. The explicit Integer equality establishes equal
addresses at one element width; a low-word equality alone is insufficient.

```click
theorem same_byte_address(bytes: uint8[], wide: uint64, index: int32) {
    requires to_integer(wide) == to_integer(index);
    ensures bytes + wide == bytes + index by {
        normalize() using { to_integer(wide) == to_integer(index); }
    }
}
theorem same_word_address(words: uint32[], wide: uint64, index: int32) {
    requires to_integer(index) == to_integer(wide);
    ensures words + index == words + wide by {
        normalize() using { to_integer(index) == to_integer(wide); }
    }
}
```

```expect
pass
```
