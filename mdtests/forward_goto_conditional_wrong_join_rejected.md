# conditional goto does not discard the jumping path

The cleanup label is reached with `value == 1` on the jump path, so the
fallthrough path's `value == 2` fact cannot become a fact of their join. The
omitted proof's implicit tail splits at the `if`, and the claim fails on the
jump path.

```c filename=forward_goto_conditional_wrong_join.c
int32 conditional_cleanup_wrong_join(int32 failed) {
    int32 value;
    value = 1;
    if (failed)
        goto cleanup;
    value = 2;
cleanup:
    return value;
}
```

```click
verifying "forward_goto_conditional_wrong_join.c";

int32 conditional_cleanup_wrong_join(int32 failed) {
    ensures result == 2;
}
```

```expect
fail: `ensures result == 2` failed for `conditional_cleanup_wrong_join.ensures_0` path 0: unclosed goal: result == 2; left side evaluated to 1
```
