# Native C++ scalar-member domain: local

The native C++ importer applies the same selected-object domain checks.

```cpp filename=probe.cpp function=probe profile=scalar_int32
struct Pair { int first; int second; };
int probe(Pair& p) { int* q = &p.first; q = q + 1; return *q; }
```

```click
verifying "probe.cpp";
int32 probe(Pair& p) {
    views p.first;
    views p.second;
    ensures result == p.second;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior
```
