# A compound addition bridge still requires its outer overflow guard

```click
import click::integer;

theorem missing(a: int32, b: int32, c: int32) {
    requires defined(a + b);
    ensures a == a by {
        apply(int32_add_to_integer(a + b, c));
        assumption();
    }
}
```

```expect
fail: required exact fact for theorem `click::integer::int32_add_to_integer` is unavailable
```
