# simp reads a bound inside a requires conjunction

`x + 1 >= 0` needs both of `x`'s bounds: `x >= 0` for the sign and
`x <= 100` so the increment cannot overflow. Written as one conjunction, the
upper bound is held only as a conjunct, not as a fact of its own. Simp finds
it through `x`'s indexed bound bucket and adds it to the path facts with a
checked `extract` before the arithmetic certificate cites it, just as
separate `requires` lines would provide it.

```c filename=simp_reads_a_bound_inside_a_requires_conjunction.c
int32 inc(int32 x) {
    return x + 1;
}

int32 inc_extracted(int32 x) {
    return x + 1;
}
```

```click
verifying "simp_reads_a_bound_inside_a_requires_conjunction.c";

int32 inc(int32 x) {
    requires x >= 0 and x <= 100;
    ensures result >= 0;
} by { execute(); simp(); }

int32 inc_extracted(int32 x) {
    requires x >= 0 and x <= 100;
    ensures result >= 0;
} by {
    execute();
    extract(x <= 100);
    simp();
}
```

```expect
pass
```
