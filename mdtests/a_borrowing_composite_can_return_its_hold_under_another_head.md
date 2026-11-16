# A borrowing composite can return its hold under another head

The call to `repack` consumes one borrowing head and produces another over the
same viewed bytes. The returned occurrence keeps the selected input hold alive;
consuming it then recovers the owner so the caller can write the bytes again.

```c filename=borrowing_repack.c
void f(int32* p) {
    pack(p);
    repack(p);
    drop(p);
    p[0] = 1;
}
```

```click
verifying "borrowing_repack.c";

resource first_reader(p: int32*) {
    views p[0..1];
}

resource second_reader(p: int32*) {
    views p[0..1];
}

extern void pack(int32* p) {
    views p[0..1];
    produces first_reader(p);
}

extern void repack(int32* p) {
    consumes first_reader(p);
    produces second_reader(p);
}

extern void drop(int32* p) {
    consumes second_reader(p);
}

void f(int32* p) {
    owns p[0..1];
}
```

```expect
pass
```
