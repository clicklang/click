# The integer arithmetic directive is refused

Specification arithmetic is over `Integer` in every file, so the former
migration directive `arithmetic "integer";` is refused rather than read.

```click
arithmetic "integer";

theorem trivial(x: int32) {
    ensures x == x;
}
```

```expect
fail: remove the `arithmetic` directive
```
