# structural induction patterns bind every constructor field

```click
spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}

theorem rejected(xs: TestList<int32>) {
    ensures xs == xs by {
        let ih = induct(xs);
        match xs {
            TestList::Nil => {
                solve();
            }
            TestList::Cons(tail) => {
                solve();
            }
        }
    }
}
```

```expect
fail: proof `match` pattern has the wrong number of fields
```
