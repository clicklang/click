# Even unused pure functions check their declared scalar return type

```click
function wrong(p: int32*) -> int32 { p }
theorem unrelated() { ensures 1 == 1 by normalize(); }
```

```expect
fail: function `wrong` returns int32, but its body can produce `p` of type int32*
```
