# Inferred array lengths still bound element accesses

The initializer creates two elements. The next element is outside the object.

```c filename=bad.c
int bad(void) {
    int values[] = { 10, 20 };
    return values[2];
}
```

```click
verifying "bad.c";
int32 bad() { ensures result == 0; }
```

```expect
fail: viewable(((byte_offset("bad.c"::bad.local(0).storage(implicit), 8)) as (uint8 *))[0..4])
```
