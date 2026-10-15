# A nested member pointer cannot read its sibling

A member reached through an embedded struct, or through an element of a
struct array, designates that member alone: one past `inner.first` is not
`inner.second`, and one past `items[1].first` is not `items[1].second`.

```c filename=probe.c
struct Pair { int32 first; int32 second; };
struct Outer { int32 tag; struct Pair inner; };
int32 nested(struct Outer* o) { return *(&o->inner.first + 1); }
int32 element(struct Pair* items) { return *(&items[1].first + 1); }
```

```click
verifying "probe.c";
int32 nested(struct Outer* o) {
    views o->inner.first;
    views o->inner.second;
    ensures result == o->inner.second;
} by { execute(); simp(); }
int32 element(struct Pair* items) {
    views items[0..2];
    ensures 1 == 1;
} by { execute(); simp(); }
```

```expect
fail: access outside the subobject the pointer designates
```
