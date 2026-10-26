# structural induction patterns bind every constructor field

```click
spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}

theorem rejected(xs: TestList<int32>) {
    ensures xs == xs by {
        induct(xs) as ih {
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
fail: pattern `TestList::Cons` expects 2 binding(s), got 1
```
