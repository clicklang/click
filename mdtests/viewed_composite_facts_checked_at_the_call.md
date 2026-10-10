# a viewed composite's facts are checked at the call

A caller that owns a composite's frontier piecewise may lend it to a callee
that `views` the composite. The call materializes the composite from those
pieces, which is sound only if the composite's facts already hold in the
caller, since `observe` publishes them inside the callee. Here the caller's
precondition establishes `c->len <= c->cap` at the call, so the adapter
admits the loan. This exercises the fact check of the materialized lending
form, and catches an adapter that refuses a loan whose facts do hold.

```c filename=viewed_composite_facts_checked_at_the_call.c
struct counter {
    int32 len;
    int32 cap;
};

int32 counter_len(struct counter* c) {
    return c->len;
}

int32 counter_len_caller(struct counter* c) {
    return counter_len(c);
}
```

```click
resource counter_storage(c: struct counter*) {
    owns c->len;
    owns c->cap;
    fact c->len <= c->cap;
}

verifying "viewed_composite_facts_checked_at_the_call.c";

int32 counter_len(struct counter* c) {
    views counter_storage(c);
    ensures result == c->len;
} by {
    execute();
    simp();
}

int32 counter_len_caller(struct counter* c) {
    owns c->len;
    owns c->cap;
    requires c->len <= c->cap;
    ensures result == c->len;
} by {
    execute();
    simp();
}
```

```expect
pass
```
