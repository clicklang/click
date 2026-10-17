# A C++ member reference returned by a call keeps its subobject

`first` returns a reference to `pair.first`. The caller binds it and reads
one past its address, where `second` lives; the reference designates only
`first`.

```cpp filename=refr.cpp function=caller profile=normal_only
struct Pair { int first; int second; };
int& first(Pair& pair) noexcept { return pair.first; }
int caller(Pair& pair) noexcept { int& r = first(pair); return *(&r + 1); }
```

```click
verifying "refr.cpp";
int32& first(struct Pair& pair) {
    views pair.first;
    ensures &result == &pair.first;
} by { execute(); simp(); }
int32 caller(struct Pair& pair) {
    views pair.first;
    views pair.second;
    ensures result == pair.second;
} by { execute(); simp(); }
```

```expect
fail: access outside the subobject the pointer designates
```
