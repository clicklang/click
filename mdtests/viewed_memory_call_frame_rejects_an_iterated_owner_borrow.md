# A call cannot borrow a view from an iterated owner it also transfers

```c filename=iterated_view_conflict.c
void touch(int32* flags, int32* data, int32 n) {
    data[0] = 1;
}

int32 keep(int32* flags, int32* data, int32 n, int32* b) {
    touch(flags, data, n);
    touch(flags, data, n);
    return *b;
}
int32 root(int32* flags, int32* b) {
    return keep(flags, b, 1, b);
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

verifying "iterated_view_conflict.c";

void touch(int32* flags, int32* data, int32 n) {
    owns cells(flags, data, n);
    requires n == 1;
    requires flags[0] == 0;
    ensures flags[0] == 0;
} by {
    unfold(cells(flags, data, n));
    take(data[0..1]);
    step();
    have flags[0] == 0 by simp();
    give(data[0..1]);
    fold(cells(flags, data, n));
    execute();
    simp();
}

int32 keep(int32* flags, int32* data, int32 n, int32* b) {
    owns cells(flags, data, n);
    views *b;
    requires n == 1;
    requires flags[0] == 0;
    ensures result == old(*b);
} by {
    mark m0;
    step();
    step();
    have *b == old(*b) by {
        transport(at(m0, *b) == old(*b), *b == old(*b)) using {
            at(m0, *b) == old(*b);
        };
    }
    execute();
    simp();
}
int32 root(int32* flags, int32* b) {
    owns cells(flags, b, 1);
    requires flags[0] == 0;
    ensures result == old(*b);
} by {
    execute();
    simp();
}
```


```expect
fail: stable-view
```
