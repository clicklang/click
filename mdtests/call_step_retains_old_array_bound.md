# A call step retains the original snapshot of its array-element bound

A write to `visited` leaves `left` unchanged. The observed resource supplies
the bound at the current snapshot; the call reads the same cell through its
entry snapshot. Keep the call theorem's original bound when transporting its
facts to the statement exit.

```c filename=probe.c
int32 probe(int32 *left, int32 *visited, int32 n, int32 cur) {
    visited[cur] = 1;
    return use(left[cur]);
}
```

```click
verifying "probe.c";
resource bounded(left: int32*, n: int32) {
    views left[0..n];
    fact forall (k: int32) { 0 <= k and k < n implies 0 <= left[k] and left[k] < n };
}
extern int32 use(int32 x) {
    requires 0 <= x;
    ensures result == x;
}
int32 probe(int32 *left, int32 *visited, int32 n, int32 cur) {
    requires 0 <= cur;
    requires cur < n;
    requires n <= 1073741823;
    views bounded(left, n);
    owns visited[0..n];
    requires separate(memory(left[0..n]), memory(visited[0..n]));
    ensures result >= 0;
} by {
    step();
    observe(bounded(left, n));
    have 0 <= left[cur] and left[cur] < n by {
        instantiate(forall (k: int32) { 0 <= k and k < n implies 0 <= left[k] and left[k] < n }, cur);
        assumption();
    }
    let { result: value } = step(use(left[cur]), {});
    step(); simp();
}
```

```expect
pass
```
