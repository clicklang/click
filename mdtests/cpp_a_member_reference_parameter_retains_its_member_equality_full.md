# A member reference retains the bounds of its field

Binding `r` to `pair.first` carries the selected member extent into the call,
so its address equals the contract's spelling of that same member.

```cpp filename=refp.cpp function=caller profile=normal_only
struct Pair { int first; int second; };
int reach(Pair& pair, int& r) noexcept { return *(&r + 0); }
int caller(Pair& pair) noexcept { return reach(pair, pair.first); }
```

```click
verifying "refp.cpp";
int32 reach(struct Pair& pair, int32& r) {
    views pair.first;
    views pair.second;
    requires &r == &pair.first;
    ensures result == pair.first;
} by { execute(); simp(); }
int32 caller(struct Pair& pair) {
    views pair.first;
    views pair.second;
    ensures result == pair.first;
} by { execute(); simp(); }
```

```expect
pass
```
