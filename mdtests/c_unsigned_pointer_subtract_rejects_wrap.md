# A huge unsigned offset cannot wrap into an in-bounds displacement

The omitted proof's implicit tail steps the subtraction and refuses it as
undefined behavior instead of wrapping the offset back to `&cells[2]`.

```c filename=offset_wrap.c
int32 run() {
    int32 cells[3];
    int32* p = &cells[1];
    int32* q = p - 18446744073709551615UL;
    return q == &cells[2];
}
```

```click
verifying "offset_wrap.c";
int32 run() { ensures result == 1; }
```

```expect
fail: `step()` produced undefined behavior: pointer arithmetic left the pointed-to object
```
