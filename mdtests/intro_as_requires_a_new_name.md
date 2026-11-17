# Named intro requires a new name

`let name = intro()` cannot reuse an active value binding. `n` is already the theorem's parameter, so
introducing the goal's variable as `n` is refused where it is written.

```click
theorem intro_as_clash(n: int32) {
    ensures forall (a: int32) { a == a } by {
        let n = intro();
        normalize();
    }
}
```

```expect
fail: `n` is already in scope here; choose a name that is not
```
