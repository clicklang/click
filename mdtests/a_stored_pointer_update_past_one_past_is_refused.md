# A compound update cannot take a stored pointer beyond one past its array

```c filename=cursor_past_end.c
void advance(int **slot, int *buffer)
{
    *slot = buffer;
    *slot += 3;
}
```

```click
verifying "cursor_past_end.c";

void advance(int32** slot, int32* buffer) {
    owns slot[0..1];
    views buffer[0..2];
}
```

```expect
fail: pointer arithmetic
```
