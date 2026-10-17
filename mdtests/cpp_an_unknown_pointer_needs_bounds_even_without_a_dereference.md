# An unknown C++ pointer needs formation bounds without a dereference

```cpp filename=formation.cpp function=probe profile=normal_only
int* probe(int* p) noexcept { return p + 1; }
```

```click
verifying "formation.cpp";
int32* probe(int32* p) {
    ensures true;
} by { execute(); simp(); }
```

```expect
fail: pointer arithmetic left the pointed-to object
```
