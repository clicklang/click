# A predicate cannot take a built-in form's name

`defined(x)` is the built-in definedness form, so a predicate named
`defined` could never be called. Before, the declaration was accepted and
every `defined(x)` read the built-in form: this theorem verified though the
predicate it names says `x == 1` and `x` is 5.

```click
predicate defined(x: int32) { x == 1 }

theorem t(x: int32) {
    requires x == 5;
    ensures defined(x) by auto();
}
```

```expect
fail: `defined(...)` is a built-in form, so a predicate named `defined` could never be called
```
