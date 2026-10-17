# Native bounds survive refolding their memory resource

The pointer's bounds remain known after its bytes are hidden again. Pointer
formation needs those bounds, while reading still needs byte authority.

```c filename=buffer.c
uint8* end(uint8* p, uint64 n) { return p + n; }
```

```click
resource buffer(p: uint8*, n: uint64) {
    owns p[0u64..n];
}
verifying "buffer.c";
uint8* end(uint8* p, uint64 n) {
    owns buffer(p, n);
    ensures result == p + n;
} by {
    unfold(buffer(p, n));
    fold(buffer(p, n));
    execute(); simp();
}
```

```expect
pass
```
