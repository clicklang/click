# Separately proved claims share one entry state in authority mode

Each claim here has its own proof. Every proof of a function starts from the
same entry context, built once, so the claims' completions carry the same
creation ledger and stable-view loan identities and certify against one
entry state.

```c filename=select.c
int32 *select(int32 *result, int32 *next) { return next; }
```

```click
verifying "select.c";
int32 *select(int32 *result, int32 *next) {
    views result[0..1];
    views next[0..1];
    requires c(result)[0] == 3 and next[0] == 7;
    ensures load_int32(c(result)) == 3 by auto;
    ensures *c(result) == 3 by auto;
    ensures byte_offset(c(result), 0) == c(result) by auto;
    ensures address(c(result)) == address(c(result)) by auto;
    ensures result[0] == 7 by auto;
}
```

```expect
pass
```
