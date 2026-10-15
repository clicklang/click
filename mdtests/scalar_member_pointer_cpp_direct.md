# Native C++ scalar-member domain: direct

The native C++ importer applies the same selected-object domain checks.

```cpp filename=probe.cpp function=probe profile=scalar_int32
struct Pair { int first; int second; };
int probe(Pair& p) { return *(&p.first + 1); }
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
