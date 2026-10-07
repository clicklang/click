# List-valued named members preserve fields and private memory across a helper

```c filename=list_field_helper.c
void bump(int32* pool, int32* p) { p[0] = 7; }
int32 run() {
    int32 pool = 0;
    int32* p = malloc(8);
    if (p == 0) return 0;
    p[0] = 1;
    p[1] = 2;
    bump(&pool, p);
    int32 result = p[0] + p[1];
    free(p);
    return result;
}
```

```click resource_semantics=authority
authorized resource ticket(pool: int32*, p: int32*) {
    field model: List<int32>;
    owns p[0..1];
}
resource control(pool: int32*) { owns authority(ticket(pool, _)); }
verifying "list_field_helper.c";
void bump(int32* pool, int32* p) {
    owns member: ticket(pool, p);
    ensures member.model == old(member.model);
    ensures p[0] == 7;
} by { unfold(member); step(); fold(member); execute(); simp(); }
int32 run() { ensures result == 0 or result == 9; } by {
    step(); step(); step(); step();
    branch then { execute(); simp(); } else {}
    step(); step();
    fold(authority(ticket(&pool, _)));
    let first = fold(ticket(&pool, p), { model: List<int32>::Cons(1, List<int32>::Nil) });
    let second = fold(ticket(&pool, p + 1), { model: List<int32>::Cons(2, List<int32>::Nil) });
    fold(control(&pool));
    step(bump(&pool, p), { member: first });
    have first.model == List<int32>::Cons(1, List<int32>::Nil) by simp;
    have second.model == List<int32>::Cons(2, List<int32>::Nil) by simp;
    unfold(control(&pool));
    have count(ticket(&pool, _)) == 2 by simp;
    have count(ticket(&pool, p)) == 1 by simp;
    unfold(first); unfold(second);
    unfold(authority(ticket(&pool, _)));
    execute(); simp();
}
```

```expect
pass
```
