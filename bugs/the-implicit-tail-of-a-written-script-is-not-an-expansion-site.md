# The implicit tail of a written script is not an expansion site

## Violated invariant

Every smart site is selectable by location and audited. `click profile` and
`docs/reference/cli/expand.md` name the implicit tail that ends every script as
a smart site, and an omitted proof's tail is one: `click expand FILE:LINE` at
the claim (or at the closing brace of a grouped contract) expands it, and
`click audit` counts it. A written script that stops with C left also ends in
the implicit tail, which runs the rest of the C and closes the goals, but that
tail is not a site. `click expand` refuses every line of the script with "no
smart tactic starts on this line", and `click audit` discovers no site for it,
so its expansion is never checked. Only `click expand --claim` reaches it.

Before `execute()` was removed, such scripts usually wrote `execute();` at
their end, which was a site. The migration deleted those trailing
`execute(); solve();` uses, so their tails lost audit coverage.

## Reproduction

`f.c`:

```c
int32 f(int32 x) {
    int32 y = x;
    if (x < 0) {
        return 0;
    }
    return y;
}
```

```click
verifying "f.c";

int32 f(int32 x) {
    ensures result >= 0 or x < 0;
} by {
    step();
}
```

`click verify` passes. `click expand f.click:6` and `click expand f.click:7`
report "no smart tactic starts on this line", and `click audit f.click`
reports "0 sites discovered". With the `by` block removed, `click audit`
discovers and passes 1 site. A proof `if` whose arms stop with C left behaves
the same way: each arm's tail is not a site.

## Intended regression

A test in `src/surface/expansion/tests.rs` or `src/bin/click-audit/tests.rs`
with the script above: the tail is listed by
`c0_smart_tactic_source_sites`, a location after `step();` selects it, and
its expansion verifies. The same for a tail that ends an arm of a proof `if`.

## Acceptance criteria

- The implicit tail of a written script, and of each arm or case that ends
  a script, is a smart site, anchored after the script's or arm's last
  written tactic, and `click profile` names the same location.
- `click expand` at that location writes the tail's steps, splits and
  closers in place, and the rewrite verifies.
- `click audit` discovers and checks these sites.
