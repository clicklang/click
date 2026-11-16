# A copied unsigned-word pointer grants no backing read permission

```c filename=word_view.c
struct word_view { uint32* data; uint64 size; };
uint32* data(struct word_view v) { return v.data; }
uint32 read(uint32* p) {
    struct word_view v = {p, 1};
    return *data(v);
}
```

```click
verifying "word_view.c";
uint32* data(struct word_view v) { ensures result == v.data; }
uint32 read(uint32* p) { ensures true; }
```

```expect
fail: missing resource
```
