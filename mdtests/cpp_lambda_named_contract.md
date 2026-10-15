# A C++ lambda passed for a function pointer meets its named contract

A lambda that captures nothing converts to a function pointer, and the
converted value is its call operator's address. The sidecar names the call
operator by its enclosing function and its index among the lambdas written
there, `caller::(lambda#0)`, and verifies it like any function; the caller
passing it shows it meets the contract `apply` requires of its pointer.

```cpp filename=lambda.cpp function=caller profile=normal_only
int apply(int (*f)(int) noexcept, int x) noexcept { return f(x); }
int caller(int x) noexcept {
    return apply([](int y) noexcept { return y + y; }, x);
}
```

```click
verifying "lambda.cpp";
contract int Doubling(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}
int apply(int (*f)(int), int x) {
    requires Doubling(f);
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
} by { execute(); simp(); }
int caller::(lambda#0)(int y) {
    requires 0 <= y and y <= 1000;
    ensures result == y + y;
} by { execute(); simp(); }
int caller(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
} by { execute(); simp(); }
```

```expect
pass
```
