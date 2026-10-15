# a file may declare a function with a library function's name

`list::append` has a qualified identity, so a file's own `append` is a
different function, and the library's is still reached by its path.

```click
function append(x: int32) -> int32 {
    x + 1
}

theorem own_append() {
    ensures append(1) == 2 by {
        unfold(append(1));
        simp();
    }
}

theorem library_append(xs: List<int32>) {
    ensures list::append(List<int32>::Nil, xs) == xs by {
        apply(list::append_left_identity(xs));
    }
}
```

```expect
pass
```
