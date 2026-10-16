# pointer-to-pointer out parameters

Pointer-valued cells use the platform pointer width, while the pointers stored
in those cells retain the element width of their own pointees.

```c filename=publish_int32.c
int32 publish_int32(int32** out, int32* source[]) {
    *out = source[0];
    return 0;
}
```

```c filename=publish_uint8.c
int32 publish_uint8(uint8** out, uint8* source[]) {
    *out = source[0];
    return 0;
}
```

```click
verifying "publish_int32.c";

int32 publish_int32(int32** out, int32* source[]) {
    owns out[0..1] by auto();
    owns source[0..1] by auto();

    ensures out[0] == source[0];
    ensures result == 0;
}

verifying "publish_uint8.c";

int32 publish_uint8(uint8** out, uint8* source[]) {
    owns out[0..1] by auto();
    owns source[0..1] by auto();

    ensures out[0] == source[0];
    ensures result == 0;
}
```

```expect
pass
```
