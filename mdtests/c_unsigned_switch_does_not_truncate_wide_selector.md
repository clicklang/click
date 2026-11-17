# A switch must not silently truncate a wider selector

The selector is 2^32 + 1, so the C program returns zero. The 32-bit switch
model must refuse this unsupported selector rather than truncating it to one
and proving the false result seven.

```c filename=wide.c
int wide(unsigned long value) {
    switch (value) {
        case 1u: return 7;
        default: return 0;
    }
}
```

```click
verifying "wide.c";
int32 wide(uint64 value) {
    requires value == 4294967297u64;
    ensures result == 7;
}
```

```expect
fail: type mismatch
```
