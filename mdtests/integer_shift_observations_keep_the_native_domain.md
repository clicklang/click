# Explicit native domain of an Integer shift observation
```click
theorem shift(x: int32) {
    requires 0 <= x;
    requires x <= 100;
    ensures to_integer(x << 2) <= 400 by {
        have x <= 536870911 by { solve() using { x <= 100; }; }
        have -2147483648 <= to_integer(x) * 4 by { solve() using { 0 <= x; x <= 100; }; }
        have to_integer(x) * 4 <= 2147483647 by { solve() using { 0 <= x; x <= 100; }; }
        have to_integer(x << 2) == to_integer(x) * 4 by known();
        solve() using { to_integer(x << 2) == to_integer(x) * 4; x <= 100; 0 <= x; x <= 536870911; };
    }
}
```
```expect
pass
```
