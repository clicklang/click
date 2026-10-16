# A refolded child keeps its family across proof branches

```c filename=child.c
void preserve(int32* p, int32 flag) {}
```

```click
verifying "child.c";
resource cell(p: int32*) {
    field value: int32;
    owns *p;
    fact *p == value;
}
resource box(p: int32*) {
    field value: int32;
    owns item: cell(p);
    fact item.value == value;
}
void preserve(int32* p, int32 flag) {
    owns parent: box(p);
    ensures parent.value == old(parent.value);
} by {
    let { item: item } = unfold(parent);
    unfold(item);
    let item = fold(cell(p), { value: old(parent.value) });
    let parent = fold(box(p), { value: old(parent.value) }, { item: item });
    if flag == 0 {
        let { item: item } = unfold(parent);
        unfold(item);
        let replacement = fold(cell(p), { value: old(parent.value) });
        let parent = fold(box(p), { value: old(parent.value) }, { item: replacement });
        execute();
    } else {
        let { item: item } = unfold(parent);
        let parent = fold(box(p), { value: old(parent.value) }, { item: item });
        execute();
    }
}
```

```expect
pass
```
