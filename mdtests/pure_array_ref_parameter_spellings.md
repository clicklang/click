# pure Click array-ref parameters follow C pointer and array spellings

This checks that a pure Click function or predicate parameter written as
`p: int32[]` or `p: int32*` is a Click array ref that can be indexed.

```c filename=sorted_pair_count.c
int32 sorted_pair_count(int32 p[2], int32 x) {
    return 0;
}
```

```click
verifying "sorted_pair_count.c";

function count_matches(p: int32[], lo: int32, hi: int32, x: int32) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}

predicate sorted(p: int32*, n: int32) {
    n == 2 and p[0] <= p[1]
}

int32 sorted_pair_count(int32 p[2], int32 x) {
    requires viewable(p[0..2]);
    requires p[0] <= p[1];
    requires p[0] == x;
    ensures sorted_pair: sorted(p, 2) by {
        execute();
        unfold(sorted);
        simp();
    }
    ensures counted: count_matches(p, 0, 1, x) == 1 by auto;
}
```

```expect
pass
```
