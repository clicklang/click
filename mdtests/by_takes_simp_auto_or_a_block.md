# by takes simp, auto or a block

Only `by simp;` and `by auto;` are written without a block. Any other tactic
after `by`, with or without its call, is refused with the block to write.

```click
theorem missing_call(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by assumption();
}
```

```expect
fail: expected a proof after `by`, got `assumption`: a proof written as tactics needs a block, `by { assumption(...); }`
```
