# A whole global struct does not cover the object its address points at

Soundness: incomplete. The verifier refuses a valid call; it never accepts a
false claim.

`owns g;` on a file-scope struct names the object's storage, and
`owns *p;` names the object `p` points at. When `p == &g` the two are the
same bytes, but `owns g` is held as one struct-wide cell and `*p` as the
object's `int32` cells, so a function that owns `g` cannot pass `&g` to a
callee that owns `*p`.

Reproduced on master `943b72c` with `examples/pcg-basic` after writing
`owns pcg32_global;` in `pcg32_srandom` and `owns *rng;` in
`pcg32_srandom_r`:

```text
missing resource fact `owns pcg32_global#file-static:pcg_basic.c[0..4]`
held `owns pcg32_global#file-static:pcg_basic.c[0..1]` does not cover `pcg32_global#file-static:pcg_basic.c[0..4]`
```

The per-field spelling the example uses today, `owns pcg32_global.state;
owns pcg32_global.inc;`, fails the same way against `owns *rng;`, so the
helpers keep per-field contracts. The diagnostic also prints cells and the internal file-static name instead
of places.

Acceptance: `examples/pcg-basic` verifies with `owns pcg32_global;` in the
public wrappers and `owns *rng;` in the helpers; the diagnostic for a
missing whole global names `pcg32_global`.
