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
    requires 0 < remaining and remaining <= bytes_len as uint32 as int32;
    requires 0 <= to_integer((remaining - 1));
    requires to_integer((remaining - 1)) < to_integer(bytes_len as uint32 as int32);
    requires defined(remaining - 1);
    views bytes[0..bytes_len as uint32 as int32];
    ensures result == old(bytes[remaining - 1] as int32);
} by {
    have 0 <= bytes_len as uint32 as int32;
    have defined(bytes[remaining - 1]) by {
        transport(at(function.entry, viewable(bytes[0..bytes_len as uint32 as int32])), defined(bytes[remaining - 1])) using {
            at(function.entry, viewable(bytes[0..bytes_len as uint32 as int32]));
            0 <= bytes_len as uint32 as int32;
            defined(remaining - 1);
            0 <= to_integer(remaining - 1);
            to_integer(remaining - 1) < to_integer(bytes_len as uint32 as int32);
        };
    }
}
```
```expect
pass
```
