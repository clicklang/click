# Copying a descriptor reads its unsigned-word pointer field

Even a callee that uses only the size cannot receive a descriptor whose
pointer field has never been initialized.

```c filename=word_view.c
struct word_view { uint32* data; uint64 size; };
uint64 size(struct word_view v) { return v.size; }
uint64 uninitialized() {
    struct word_view v;
    v.size = 1;
    return size(v);
}
```

```click
verifying "word_view.c";
uint64 size(struct word_view v) { ensures result == v.size; }
uint64 uninitialized() { ensures result == 1u64; }
```

```expect
fail: uninitialized
```
