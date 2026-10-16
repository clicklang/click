# An unrelated offset equality does not disable an owned parameter store

The store is authorized by the selected array and index bounds. The offset
premise names another pointer and independent indices.

```c filename=selected_store.c
void selected_store(int32* buf, int32* other, int32 a, int32 b, int32 j) {
    buf[j] = 5;
}
```

```click
verifying "selected_store.c";

void selected_store(int32* buf, int32* other, int32 a, int32 b, int32 j) {
    owns buf[0..1000];
    requires 500 <= j and j < 1000;
    requires other + a == other + b;
    ensures buf[j] == 5 by auto();
}
```

```expect
pass
```
