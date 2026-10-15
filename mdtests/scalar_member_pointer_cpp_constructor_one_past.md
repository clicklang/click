# A native constructor preserves a scalar member's stored domain: one_past

```cpp filename=holder.cpp function=probe profile=scalar_int32
struct Pair { int first; int second; };
struct Holder { int* link; explicit Holder(int& value) noexcept : link(&value) {} };
int probe(Pair& p) { Holder h(p.first); return *(h.link + 1); }
```

```click
verifying "holder.cpp";
Holder::Holder(int32& value) {
    owns this->link;
    ensures this->link == &value;
} by { execute(); simp(); }
int32 probe(Pair& p) {
    views p.first; views p.second;
    ensures result == p.second;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior
```
