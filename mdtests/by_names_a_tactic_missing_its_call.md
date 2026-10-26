# by names a tactic missing its call

Every tactic after `by` is written with its parentheses. A
tactic name without its call is refused with the spelling to write.

```click
theorem missing_call(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by assumption;
}
```

```expect
fail: expected a proof after `by`, got `assumption`: write one tactic call such as `assumption();`, or a block `{ ... }`
```
