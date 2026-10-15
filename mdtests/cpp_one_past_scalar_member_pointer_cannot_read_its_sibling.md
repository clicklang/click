# A C++ one-past scalar-member pointer cannot read its sibling

C++ [basic.compound] treats `pair.first` as an array of one element for
pointer arithmetic, and [expr.add] permits forming the one-past pointer but
not reading through it. The member address carries `first`'s extent, so the
read at the address `second` occupies is refused.

```cpp filename=pair.cpp function=probe profile=normal_only
struct Pair { int first; int second; };
int probe(Pair& pair) noexcept { return *(&pair.first + 1); }
```

```click
verifying "pair.cpp";
int32 probe(struct Pair& pair) {
    views pair.first;
    views pair.second;
    ensures result == pair.second;
} by { execute(); simp(); }
```

```expect
fail: access outside the subobject the pointer designates
```
