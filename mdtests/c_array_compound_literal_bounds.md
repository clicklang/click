# An array compound literal has the bounds of its completed array type

```c filename=example.c
int answer(void) {
    return ((int[]){10, 20, 30})[3];
}
```

```click
verifying "example.c";
int32 answer() { ensures result == 0; }
```

```expect
fail: viewable(((byte_offset("example.c"::answer.local(0).storage(implicit), 12)) as (uint8 *))[0..4])
```
