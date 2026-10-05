# Named private custody cannot replace field-count authority

```c filename=read_cell.c
int32 read_cell(int32* p);
int32 run() {
    int32* p = malloc(4);
    if (p == 0) return 0;
    p[0] = 7;
    read_cell(p);
    free(p);
    return 0;
}
```

```click resource_semantics=authority
resource cell(p: int32*) {
    field model: List<int32>;
    owns p[0..1];
}

resource control(p: int32*) { owns authority(cell(p)); }

verifying "read_cell.c";

extern int32 read_cell(int32* p) {
    owns authority(cell(p));
    owns member: cell(p);
    requires count(cell(p)) == 1;
    ensures member.model == old(member.model);
    ensures count(cell(p)) == old(count(cell(p)));
}

int32 run() { ensures result == 0; } by {
    step(); step();
    branch { then { execute(); simp(); } else {} }
    step();
    fold(authority(cell(p)));
    let first = fold(cell(p), { model: List<int32>::Cons(7, List<int32>::Nil) });
    fold(control(p));
    have count(cell(p)) == 1 by simp;
    step(read_cell(p), { member: first });
    have first.model == List<int32>::Cons(7, List<int32>::Nil) by simp;
    have count(cell(p)) == 1 by simp;
    unfold(first);
    unfold(authority(cell(p)));
    execute(); simp();
}
```

```expect
fail: count(...) requires owning authority for that population
```
