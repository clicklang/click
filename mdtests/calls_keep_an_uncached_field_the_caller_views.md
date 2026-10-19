# Consecutive calls keep an uncached cell the caller views

`keep` retains its view of `b->v` across both calls. Transferring the `cells`
resource does not end that view: the checked call transition excludes writes
that conflict with it. Each recorded frame therefore preserves the uncached
read, and the original transport proof checks across both calls.

```c filename=calls_keep_an_uncached_field_the_caller_views.c
struct box {
    int32 v;
};

void touch(int32* flags, int32* data, int32 n) {
    return;
}

int32 keep(int32* flags, int32* data, int32 n, struct box* b) {
    touch(flags, data, n);
    touch(flags, data, n);
    return b->v;
}
```

```click
resource cells(flags: int32*, data: int32*, n: int32) {
    owns flags[0..n];
    forall (k: int32) where 0 <= k and k < n {
        if flags[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

verifying "calls_keep_an_uncached_field_the_caller_views.c";

void touch(int32* flags, int32* data, int32 n) {
    owns cells(flags, data, n);
} by {
    execute();
    simp();
}

int32 keep(int32* flags, int32* data, int32 n, struct box* b) {
    owns cells(flags, data, n);
    views b->v;
    ensures result == old(b->v);
} by {
    mark m0;
    step();
    step();
    have b->v == old(b->v) by {
        transport(at(m0, b->v) == old(b->v), b->v == old(b->v)) using {
            at(m0, b->v) == old(b->v);
        };
    }
    execute();
    simp();
}
```

```expect
pass
```
