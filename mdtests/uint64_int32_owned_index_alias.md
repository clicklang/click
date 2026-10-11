# A native index and its exact signed observation access one owned cell

Prove the address equality before executing the native-width store. The later
signed-index read returns the stored value under the original ownership.

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
uint8 byte_write_read(uint8 *bytes, uint64 wide, int32 index, uint8 value) {
    requires to_integer(wide) == to_integer(index);
    owns bytes[index];
    ensures result == value;
} by {
    have bytes + wide == bytes + index by {
        normalize() using { to_integer(wide) == to_integer(index); }
    }
    execute(); simp();
}
uint32 word_write_read(uint32 *words, uint64 wide, int32 index, uint32 value) {
    requires to_integer(index) == to_integer(wide);
    owns words[index];
    ensures result == value;
} by {
    have words + index == words + wide by {
        normalize() using { to_integer(index) == to_integer(wide); }
    }
    execute(); simp();
}
```

```expect
pass
```
