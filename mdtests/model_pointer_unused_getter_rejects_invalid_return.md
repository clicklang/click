# An unused pointer getter still checks its return type

There is no call or model construction to trigger argument checking. The
definition itself must reject its incompatible return value.

```click
function wrong(p: struct other*) -> struct node* { p }
theorem unrelated() { ensures 1 == 1 by normalize(); }
```

```expect
fail: function `wrong` return value requires original object class `struct node` or null
```
