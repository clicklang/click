# An unknown pointer needs bounds even without a dereference

```c filename=probe.c
int32* probe(int32* p) { return p + 1; }
```

```click
verifying "probe.c";
int32* probe(int32* p) {
    ensures true;
} by { execute(); simp(); }
```

```expect
fail: pointer arithmetic left the pointed-to object
```
