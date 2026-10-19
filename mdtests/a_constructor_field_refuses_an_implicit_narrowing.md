# A constructor field refuses an implicit narrowing

Not every `int64` is an `int32`, so `y: int64` does not convert to
`Seq<int32>`'s field implicitly: the narrowing can change the value, and is
written, as `(int32) y` or the checked `to_int32(y)`.

```click
spec enum Seq<T> {
    Nil,
    Cons(T, Seq<T>),
}

function narrow(y: int64) -> Seq<int32> {
    Seq<int32>::Cons(y, Seq<int32>::Nil)
}
```

```expect
fail: constructor `Seq::Cons` argument 0 expects int32, got int64 in function `narrow`; a conversion that can change the value is written
```
