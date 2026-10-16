# integer arithmetic is declared once

```click
arithmetic "integer";
arithmetic "integer";

theorem trivial(x: int32) {
    ensures x == x;
}
```

```expect
fail: declares `arithmetic` more than once
```
