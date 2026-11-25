# `obtain` opens only the existential it names

`let name = obtain(exists (k: Type) { P });` looks up the argument as an
available fact, up to the binder's name. It does not normalize the body: an
available `exists (k: int32) { k < n }` is not opened by an `obtain` whose body
is written `n > m`. Write the body as the fact states it.

```click
theorem obtain_with_a_mirrored_body(n: int32) {
    requires exists (k: int32) { k < n };
    ensures n == n by {
        let m = obtain(exists (m: int32) { n > m });
        close();
    }
}
```

```expect
fail: required existential fact is not available
```
