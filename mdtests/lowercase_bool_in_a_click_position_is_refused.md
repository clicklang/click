# Lowercase `bool` in a Click position is refused

Click's logical type is `Bool`. A C or C++ function head restates its
declaration and keeps `bool` or `_Bool`, and a Rust sidecar writes Rust's
`bool`, but a Click function, theorem, or binder that writes `bool` is told
to write `Bool`.

```click
function flag(x: bool) -> Bool { x }
```

```expect
fail: `bool` is not a Click type; write `Bool`
```
