# An uninitialized destination is copied into beside a viewed source

`copy_n_segment_invariant` consumes `uninitialized(dst[0..n])`, so its caller
may pass a destination no one has written. The loop writes each element before
anything reads it and reads only `src`, which the function views. Both are
array parameters, so their addresses lie in one block; a read of `src` is not a
read of the unwritten destination, because a read belongs to it only through
an address built from `dst`.

```c filename=uninitialized_copy_destination.c
int32 copy_n_segment_invariant(int32 dst[], int32 src[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        dst[i] = src[i];
        i = i + 1;
    }
    return i;
}
```

```click
verifying "uninitialized_copy_destination.c";

theorem int32_le_antisymmetric(left: int32, right: int32) {
    requires left <= right;
    requires right <= left;
    ensures left == right;
}

int32 copy_n_segment_invariant(int32 dst[], int32 src[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    consumes uninitialized(dst[0..n]);
    views src[0..n];
    requires separate(memory(dst[0..n]), memory(src[0..n]));
    ensures returns_n: result == n;
    ensures source_unchanged: forall (k: int32) {
        0 <= k and k < n implies src[k] == old(src[k])
    };
    ensures copied_segment: forall (k: int32) {
        0 <= k and k < n implies dst[k] == old(src[k])
    };
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
        invariant forall (k: int32) {
            0 <= k and k < i implies dst[k] == old(src[k])
        };
        owns dst[0..n];
    }
    step();
    apply(int32_le_antisymmetric(
        at(loop(0).exit, i),
        at(loop(0).exit, n)
    )) using {
        at(loop(0).exit, i) <= at(loop(0).exit, n);
        at(loop(0).exit, n) <= at(loop(0).exit, i);
    };
    have result == n by {
        simp() using {
            at(loop(0).exit, i) == at(loop(0).exit, n);
        };
    }
    have forall (k: int32) { 0 <= k and k < n implies src[k] == old(src[k]) } by {
        have forall (k: int32) {
                at(region(0).entry, 0) <= at(region(0).entry, k) and
                at(region(0).entry, k) < at(region(0).entry, n) implies
                old(src[k]) == at(region(0).entry, src[k])
        } by {
            intro();
            intro();
            normalize();
        }
        transport(
            forall (k: int32) {
                    at(region(0).entry, 0) <= at(region(0).entry, k) and
                    at(region(0).entry, k) < at(region(0).entry, n) implies
                    old(src[k]) == at(region(0).entry, src[k])
            },
            forall (k: int32) {
                0 <= k and k < n implies old(src[k]) == src[k]
            }
        ) using {
            forall (k: int32) {
                    at(region(0).entry, 0) <= at(region(0).entry, k) and
                    at(region(0).entry, k) < at(region(0).entry, n) implies
                    old(src[k]) == at(region(0).entry, src[k])
            };
            separate(memory(dst[0..n]), memory(src[0..n]));
        };
        simp();
    }
    have forall (k: int32) { 0 <= k and k < n implies dst[k] == old(src[k]) } by {
        have forall (k: int32) {
            at(loop(0).exit, 0) <= at(loop(0).exit, k) and
                at(loop(0).exit, k) < at(loop(0).exit, n) implies
                at(loop(0).exit, dst[k]) == old(src[k])
        } by {
            rewrite(at(loop(0).exit, n) == at(loop(0).exit, i));
            assumption();
        }
        transport(
            forall (k: int32) {
                at(loop(0).exit, 0) <= at(loop(0).exit, k) and
                    at(loop(0).exit, k) < at(loop(0).exit, n) implies
                    at(loop(0).exit, dst[k]) == old(src[k])
            },
            forall (k: int32) {
                0 <= k and k < n implies dst[k] == old(src[k])
            }
        ) using {
            forall (k: int32) {
                at(loop(0).exit, 0) <= at(loop(0).exit, k) and
                    at(loop(0).exit, k) < at(loop(0).exit, n) implies
                    at(loop(0).exit, dst[k]) == old(src[k])
            };
        };
        assumption();
    }
    assumption();
    assumption();
    assumption();
}
```

```expect
pass
```
