# Nested conditional arithmetic uses explicit arm equations

```click
theorem mathematical(flag: Bool, x: Integer, y: Integer) {
    requires flag;
    requires x <= 5;
    ensures (if flag { x } else { y }) + 3 <= 8 by {
        have ((if flag { x } else { y }) : Integer) == x by known();
        rewrite(if flag { x } else { y }, x);
        close() using { x <= 5; };
    }
}

theorem observed(flag: Bool, x: int32, y: int32) {
    requires flag;
    requires x <= 5;
    ensures to_integer(if flag { x } else { y }) + 3 <= 8 by {
        have (if flag { x } else { y }) == x by known();
        rewrite(if flag { x } else { y }, x);
        close() using { x <= 5; };
    }
}

theorem casted(flag: Bool, x: int32, y: int32) {
    requires flag;
    ensures to_integer((if flag { x } else { y }) as int64) == to_integer(x) by {
        have (if flag { x } else { y }) == x by known();
        rewrite(if flag { x } else { y }, x);
        known();
    }
}
```

```expect
pass
```
