# An unsigned-word pointer field remains a value through a by-value copy

Copying the descriptor copies its pointer and count, while authority to read
its backing remains an explicit view. The copies can also carry null pointers.

```c filename=word_view.c
struct word_view { uint32* data; uint64 size; };
uint32* data(struct word_view v) { return v.data; }
uint32 read(uint32* p) {
    struct word_view v = {p, 1};
    return *data(v);
}
uint32* empty() {
    struct word_view v = {0};
    return data(v);
}
```

```click
verifying "word_view.c";
uint32* data(struct word_view v) {
    ensures result == v.data;
}
uint32 read(uint32* p) {
    views p[0..1];
    ensures result == p[0];
}
uint32* empty() {
    ensures result == 0;
}
```

```expect
pass
```
