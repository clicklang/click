# A native index and its exact signed observation access one owned cell

Exact equality with the signed index bounds the full-width index and
identifies its signed low word. The proof uses those facts to establish
address equality before executing the store. The signed-index read then
returns the stored value under the original ownership.

```c filename=alias.c
uint8 byte_write_read(uint8 *bytes, uint64 wide, int32 index, uint8 value) {
    bytes[wide] = value;
    return bytes[index];
}
uint32 word_write_read(uint32 *words, uint64 wide, int32 index, uint32 value) {
    words[wide] = value;
    return words[index];
}
```

```click
verifying "alias.c";

theorem exact_signed_index(wide: uint64, index: int32) {
    requires to_integer(wide) == to_integer(index);
    ensures wide <= 2147483647u64 and (wide as int32) == index by {
        have to_integer(wide) <= 2147483647 by {
            rewrite(to_integer(wide), to_integer(index));
            known();
        }
        have -2147483648 <= to_integer(wide) by {
            rewrite(to_integer(wide), to_integer(index));
            known();
        }
        have wide <= 2147483647u64 by known();
        have to_integer(wide as int32) == to_integer(wide) by known();
        have (wide as int32) == index by known();
        known();
    }
}

uint8 byte_write_read(uint8 *bytes, uint64 wide, int32 index, uint8 value) {
    requires to_integer(wide) == to_integer(index);
    owns bytes[index];
    ensures result == value;
} by {
    have bytes + wide == bytes + index by {
        apply(exact_signed_index(wide, index));
        have bytes + wide == bytes + (wide as int32) by known();
        rewrite(bytes + wide, bytes + (wide as int32));
        rewrite(wide as int32, index);
        known();
    }
}
uint32 word_write_read(uint32 *words, uint64 wide, int32 index, uint32 value) {
    requires to_integer(index) == to_integer(wide);
    owns words[index];
    ensures result == value;
} by {
    have words + index == words + wide by {
        apply(exact_signed_index(wide, index));
        have words + wide == words + (wide as int32) by known();
        rewrite(words + wide, words + (wide as int32));
        rewrite(wide as int32, index);
        known();
    }
}
```

```expect
pass
```
