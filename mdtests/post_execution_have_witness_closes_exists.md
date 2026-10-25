# A post-execution `have` proves an existential with `witness`

After `execute()`, a scoped `have` proves an existential about `result` with
`witness`, and the later `simp()` closes the matching postcondition from it.

```c filename=post_have_witness.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "post_have_witness.c";

int32 identity(int32 x) {
    ensures exists (k: int32) { k == result };
} by {
    step_until(function.exit);
    have exists (k: int32) { k == result } by {
        witness { k: result };
        simp();
    }
    simp();
}
```

```expect
pass
```
