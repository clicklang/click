# A spec enum pointer field needs a scalar element

A `T*` field is the pointer type of `T`'s C representation. An instance whose
`T` has none, such as `Integer`, is refused.

```click
spec enum Span<T> {
    Span(T*, uint64),
}

function len<T>(s: Span<T>) -> uint64 {
    match s {
        Span::Span(_, n) => n,
    }
}

theorem unbounded(p: uint8*, n: uint64) {
    ensures forall (s: Span<Integer>) { len(s) == len(s) };
}
```

```expect
fail: needs `T` to be a C scalar type
```
