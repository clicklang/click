# Exact index observations connect native and signed byte addresses

The exact Integer equality bounds the full-width index and identifies its
signed cast. The proof uses the bound to equate the offsets, then rewrites
the signed cast to the original index.

```click
import "uint64_int32_index_bounds.click";

theorem same_byte_address(bytes: uint8[], wide: uint64, index: int32) {
    requires to_integer(wide) == to_integer(index);
    ensures bytes + wide == bytes + index by {
        apply(exact_signed_index(wide, index));
        have bytes + wide == bytes + (wide as int32) by close();
        rewrite(bytes + wide, bytes + (wide as int32));
        rewrite(wide as int32, index);
        close();
    }
}
theorem same_word_address(words: uint32[], wide: uint64, index: int32) {
    requires to_integer(index) == to_integer(wide);
    ensures words + index == words + wide by {
        apply(exact_signed_index(wide, index));
        have words + wide == words + (wide as int32) by close();
        rewrite(words + wide, words + (wide as int32));
        rewrite(wide as int32, index);
        close();
    }
}
```

```expect
pass
```
