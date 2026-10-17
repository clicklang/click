# A C++ member reference parameter keeps its subobject

`caller` binds `reach`'s reference `r` to `pair.first`. `reach` also views
`pair.second`, but `&r + 1` is one past `first`, so reading it is refused.

```cpp filename=refp.cpp function=caller profile=normal_only
struct Pair { int first; int second; };
int reach(Pair& pair, int& r) noexcept { return *(&r + 1); }
int caller(Pair& pair) noexcept { return reach(pair, pair.first); }
```

```click
verifying "refp.cpp";
int32 reach(struct Pair& pair, int32& r) {
    views pair.first;
    views pair.second;
    requires &r == &pair.first;
    ensures result == pair.second;
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
