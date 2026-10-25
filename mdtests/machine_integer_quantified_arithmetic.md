# machine integer quantified arithmetic

```click
import click::integer;

theorem wide_successor(n: int64) {
    requires 0i64 <= n and n <= 100i64;
    ensures exists (x: int64) { x == n + 1i64 } by {
        have defined(n + 1i64);
        witness { x: n + 1i64 };
        have to_integer(n + 1i64) == to_integer(n) + to_integer(1i64) by auto();
        assumption();
    }
}

theorem byte_arithmetic(n: uint8) {
    ensures exists (x: uint8) { x + 1 == n + 1 } by {
        have defined(n + 1);
        witness { x: n };
        solve();
    }
}

theorem high_word() {
    ensures exists (x: int64) { x == 4294967296i64 and x != 0i64 } by {
        witness { x: 4294967296i64 };
        solve();
    }
}

theorem byte_range() {
    ensures forall (x: uint8) { x >= 0 and x <= 255 } by {
        intro();
        intro();
        intro();
        intro();
        both { assumption(); } and { assumption(); }
    }
}

theorem mixed() {
    ensures forall (x: int64) { forall (y: uint8) { exists (a: int64, b: uint8) { a == x and b == y } } } by {
        intro();
        intro();
        intro();
        intro();
        intro();
        witness { a: x, b: y };
        solve();
    }
}
```

```expect
pass
```
