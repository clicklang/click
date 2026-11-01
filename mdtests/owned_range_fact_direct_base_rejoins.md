# A cell taken from a symbolic range rejoins its direct base

```c filename=range.c
int read_saved(int *p, int index) { return p[index]; }
```

```click
verifying "range.c";
resource range(p: int32*) {
    field start: int32;
    field end: int32;
    owns p[start..end];
    fact 0 <= start;
    fact start < end;
}
resource cell(p: int32*) {
    field value: int32;
    owns *p;
    fact *p == value;
}
int read_saved(int *p, int index) {
    owns r: range(p);
    requires index == r.start;
    requires p[index] == 22;
    ensures result == 22;
} by {
    let { start: k, end: e } = unfold(r);
    let kept = fold(cell(p + k), { value: 22 });
    unfold(kept);
    let r = fold(range(p), { start: k, end: e });
    step();
}
```

```expect
pass
```
