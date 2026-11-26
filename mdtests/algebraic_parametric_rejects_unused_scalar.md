# A phantom type parameter does not defer proof checking

```click
theorem invalid<T>() {
    ensures 0 == 1 by close();
}
```

```expect
fail: invalid.ensures_0
```
