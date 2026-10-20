# `obtain` opens only the existential it names

`obtain (name: Type) { P }` looks up `exists (name: Type) { P }` as an
available fact, up to the binder's name. It does not normalize the body: an
available `exists (k: int32) { k < n }` is not opened by an `obtain` whose body
is written `n > m`. Write the body as the fact states it.

```click
theorem obtain_with_a_mirrored_body(n: int32) {
    requires exists (k: int32) { k < n };
    ensures n == n by {
        obtain (m: int32) { n > m }
        normalize();
    }
}
```

```expect
fail: requirement `exists (m: int32) { n > m }` not satisfied
```
