# Forming a C++ pointer two past a scalar member is refused

Pointer formation itself is bounded by the member's one-element domain: two
past `first` is refused although the address lies inside `pair` and nothing
is read through it.

```cpp filename=pair.cpp function=probe profile=normal_only
struct Pair { int first; int second; int third; };
int* probe(Pair& pair) noexcept { return &pair.first + 2; }
```

```click
verifying "pair.cpp";
int32* probe(struct Pair& pair) {
    views pair.first;
    views pair.second;
    views pair.third;
    ensures 1 == 1;
} by { execute(); simp(); }
```

```expect
fail: pointer arithmetic left the pointed-to object
```
