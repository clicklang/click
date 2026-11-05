# A generic pointer result is its argument's pointer type

A pure function `id<T>(p: T*) -> T*` binds `T` from its argument's pointee
type, and its result is then that pointer type. `id(p)` for an `int32*` `p`
is an `int32*`, so it compares with `p` directly.

```click
function id<T>(p: T*) -> T* {
    p
}

theorem id_is_its_argument(p: int32*) {
    ensures id(p) == p by { unfold(id(p)); normalize(); }
}

theorem id_of_bytes(p: uint8*) {
    ensures id(p) == p by { unfold(id(p)); normalize(); }
}
```

```expect
pass
```
