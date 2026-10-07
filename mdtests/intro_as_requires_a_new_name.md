# intro as requires a new name

`intro() as name` never shadows. `n` is already the theorem's parameter, so
introducing the goal's variable as `n` is refused where it is written.

```click
theorem intro_as_clash(n: int32) {
    ensures forall (a: int32) { a == a } by {
        intro() as n;
        normalize();
    }
}
```

```expect
fail: `n` is already in scope here; choose a name that is not
```
