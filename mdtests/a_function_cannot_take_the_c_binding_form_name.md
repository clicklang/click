# A function cannot take the earlier program-binding form's name

`c(name)` was the form that named the verified program's binding `name`; it
is now `program::name`, and `c(name)` is refused with that replacement. A pure
function named `c` could never be called: `c(n - 1)` reads as the refused
form. The declaration is refused with that reason.

```click
function c(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { c(n - 1) }
}
```

```expect
fail: `c(...)` was the program-binding form, now `program::name`, and is refused with that replacement, so a function named `c` could never be called
```
