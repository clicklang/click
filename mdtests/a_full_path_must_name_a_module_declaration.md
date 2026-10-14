# a full library path must name a declaration of its module

`click::list::list_reverse` names a module that exists but a declaration it
does not have, so the path is refused rather than read as something else.

```click
theorem reverse_nil() {
    ensures click::list::list_reverse(List<int32>::Nil) == List<int32>::Nil by simp;
}
```

```expect
fail: `click::list::list_reverse` names no declaration of Click library module `click::list`
```
