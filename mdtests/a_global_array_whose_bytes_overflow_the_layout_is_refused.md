# A global array whose bytes overflow the layout is refused

`big` has 2^30 `int32` elements. The element count fits a layout length, but
its 2^32 bytes do not. A file-scope array is refused by its byte size, as a
local array already is, instead of reaching execution with a saturated size.

```c filename=big.c
int32 big[1073741824];

int32 first(void) {
    return big[0];
}
```

```click
verifying "big.c";

int32 first() {
    ensures true;
} by {
    auto;
}
```

```expect
fail: file-scope array dimensions are too large for `big`
```
