# A pure machine witness must still prove its body

```click
theorem wrong_sum(n: int32) {
    requires 0 <= n and n <= 100;
    ensures exists (a: int32, b: int32) { a + b == n } by {
        witness(n, 1);
        close();
    }
}
```

```expect
fail: could not establish `(to_integer(n) + to_integer(1)) == to_integer(n)`
```
