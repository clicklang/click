# Computed byte reads retain their address-definedness guards

An explicit range transport must prove both arithmetic definedness and read
authority for a computed index.

```c filename=iterator_read.c
int32 iterator_read(const uint8* bytes, uint64 bytes_len, int32 remaining) {
    return (int32)bytes[remaining - 1];
}
```
```click
verifying "iterator_read.c";
int32 iterator_read(const uint8* bytes, uint64 bytes_len, int32 remaining) {
    requires bytes_len <= 1000u64;
    requires 0 < remaining and remaining <= (int32)(uint32)bytes_len;
    requires 0 <= (remaining - 1);
    requires (remaining - 1) < (int32)(uint32)bytes_len;
    requires defined(remaining - 1);
    views bytes[0..(int32)(uint32)bytes_len];
    ensures result == old((int32)bytes[remaining - 1]);
} by {
    have 0 <= (int32)(uint32)bytes_len by { simp(); }
    have defined(bytes[remaining - 1]) by {
        transport(at(function.entry, viewable(bytes[0..(int32)(uint32)bytes_len])), defined(bytes[remaining - 1])) using {
            at(function.entry, viewable(bytes[0..(int32)(uint32)bytes_len]));
            0 <= (int32)(uint32)bytes_len;
            defined(remaining - 1);
            0 <= remaining - 1;
            remaining - 1 < (int32)(uint32)bytes_len;
        }
    }
    execute(); simp();
}
```
```expect
pass
```
