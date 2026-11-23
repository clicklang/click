# `Pointer` binders

A theorem parameter, a quantifier binder and a `let` may have Click's
untyped `Pointer` type. A typed pointer converts to `Pointer` implicitly at a
`let`, and a cast to `Pointer` and back keeps the value, so a typed
pointer's round trip is the pointer itself.

```click
theorem reflexive(q: Pointer) {
    ensures q == q;
}

theorem every_pointer_is_itself() {
    ensures forall (q: Pointer) { q == q };
}

theorem round_trip(p: int32*) {
    ensures (p as Pointer) as (int32 *) == p;
}

theorem named(p: int32*) {
    ensures let q: Pointer = p; q as (int32 *) == p;
}
```

```expect
pass
```
