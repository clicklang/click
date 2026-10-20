# A function cannot take the C binding form's name

`c(name)` is the built-in form that names the verified C binding `name`, so a
pure function named `c` could never be called: `c(n - 1)` reads as that form
and fails to parse. The declaration is refused with that reason.

```click
function c(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { c(n - 1) }
}
```

```expect
fail: `c(...)` is a built-in form, so a function named `c` could never be called
```
