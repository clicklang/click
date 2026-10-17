# Mathematical Integer returns also check the definition body

```click
function wrong(p: int32*) -> Integer { p }
theorem unrelated() { ensures 1 == 1 by normalize(); }
```

```expect
fail: function `wrong` returns Integer, but its body can produce `p` of type int32*
```
