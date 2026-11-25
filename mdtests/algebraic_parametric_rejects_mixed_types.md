# Distinct arbitrary types are not interchangeable

```click
theorem invalid<T, U>(x: T, y: U) {
    ensures x == y by close();
}
```

```expect
fail: invalid
```
