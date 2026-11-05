# A spec enum field points to its type parameter

A variant field `T*` is a pointer to the type parameter's values. At an
instance it is the element's pointer type, so `Span<uint8>` holds a `uint8*`
and `Span<int32>` an `int32*`; in a generic function over `Span<T>` it stays
`T*`. Equality of two spans reduces to their fields, so equal pointers and
lengths make one span.

```click
spec enum Span<T> {
    Span(T*, uint64),
}

function len<T>(s: Span<T>) -> uint64 {
    match s {
        Span::Span(_, n) => n,
    }
}

function data<T>(s: Span<T>) -> T* {
    match s {
        Span::Span(p, _) => p,
    }
}

theorem len_of(p: uint8*, n: uint64) {
    ensures len(Span<uint8>::Span(p, n)) == n by {
        unfold(len(Span<uint8>::Span(p, n)));
        normalize();
    }
}

theorem data_of(p: int32*, n: uint64) {
    ensures data(Span<int32>::Span(p, n)) == p by {
        unfold(data(Span<int32>::Span(p, n)));
        normalize();
    }
}

theorem equal_parts_are_one_span(p: uint8*, q: uint8*, n: uint64) {
    requires p == q;
    ensures Span<uint8>::Span(p, n) == Span<uint8>::Span(q, n) by {
        rewrite(p == q);
        normalize();
    }
}
```

```expect
pass
```
