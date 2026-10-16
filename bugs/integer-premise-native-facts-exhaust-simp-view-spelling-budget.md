# Native facts filed for Integer premises exhaust `simp`'s view-spelling budget

Soundness: incomplete. A proof that verified before is now refused; nothing
false is accepted, because the refusal is a construction-budget failure,
reported as such.

Since #1166 ("File the native comparison beside an Integer observation
comparison"), an Integer comparison of exact machine observations also
files the native comparison it is equivalent to. In the pinned zlib
fixture this enlarges the context so much that a one-element view goal
no longer gets a checked source proof. `design/charon-trial/zlib/canonical.click`
and `incremental.click` verified at `bd8514be` (#1165) and fail from
`4be82873` (#1166) on; `reset.click` still verifies. The first bad commit
was found with `git bisect --first-parent` between `ec934e36` and `d69fda6a`.

The failing step is the second line of the `len == 1u64` branch of
`adler32_z` in `canonical.click`:

```click
 if len == 1u64 {
apply(zlib_seed_bounds(adler));
 have old((int32)(uint32)len) == 1 by simp();
 have viewable(buf[0u64..1u64]) by simp();
```

```text
proof error:
  `simp` failed for `adler32_z.contract`
  `viewable(buf[0u64..1u64])` is accepted by the kernel native view checker in the current proof context, but `simp` did not construct a checked source proof
construction failure: simp view premise spelling: budget exhausted: the selected view derivation contains 130 premises; source spelling permits at most 64
goal: viewable(buf[0..1u64])
```

The kernel accepts the view, so the facts are present. But the derivation
`simp` selects to spell it now cites 130 premises, presumably because the
duplicated native comparisons enter the selection. A view of one element
should not need anywhere near 64 premises. The fixture is also what
`tests/rust_release_install.rs` verifies after installing a release, through
the copies `scripts/prepare-adler32-demo.py` makes, so the `Rust frontend
release` workflow is red until this is fixed.

Reproduce from the repository root:

```sh
click verify design/charon-trial/zlib/canonical.click
```

## Acceptance

- `canonical.click` and `incremental.click` verify unchanged, without
  raising the view-spelling budget.
- The view derivation for `viewable(buf[0u64..1u64])` cites only the
  premises that bear on `buf`'s view, not the native duplicates of
  unrelated Integer premises. A regression keeps the original pattern: the
  `len == 1u64` branch after `apply(zlib_seed_bounds(adler))`.
- The `Rust frontend release` workflow passes.
