# normalize using refuses an algebraic equality it does not cite

`xs == ys` cited does not state `xs == zs`, and nothing relates `ys` to
`zs`, so the goal is refused.

```c filename=normalize_using_refuses_an_algebraic_equality_it_does_not_cite.c
void unused(void) {}
```

```click
verifying "normalize_using_refuses_an_algebraic_equality_it_does_not_cite.c";

theorem other<T>(xs: List<T>, ys: List<T>, zs: List<T>) {
    requires xs == ys;
    ensures xs == zs by { normalize() using { xs == ys; }; }
}
```

```expect
fail: `normalize using` goal did not normalize to true using the listed conditions
```
