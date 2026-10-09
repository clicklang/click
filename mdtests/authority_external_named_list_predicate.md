# An external contract preserves a List-valued count observation

```c filename=helper.c
extern void preserve(int32* pool);
int32 run() { int32 pool = 0; preserve(&pool); return 0; }
```

```click
function population(pool: int32*) -> List<int32> {
    List<int32>::Cons(count(ticket(pool)), List<int32>::Nil)
}
authorized resource ticket(pool: int32*) { field model: List<int32>; }
verifying "helper.c";
extern void preserve(int32* pool) {
    owns authority(ticket(pool));
    owns member: ticket(pool);
    requires count(ticket(pool)) == 1;
    requires population(pool) == List<int32>::Cons(1, List<int32>::Nil);
    ensures member.model == old(member.model);
    ensures population(pool) == old(population(pool));
    ensures count(ticket(pool)) == old(count(ticket(pool)));
}
int32 run() { ensures result == 0; } by {
    step(); step();
    fold(authority(ticket(&pool)));
    let first = fold(ticket(&pool), { model: List<int32>::Cons(7, List<int32>::Nil) });
    unfold(population(&pool));
    have count(ticket(&pool)) == 1;
    have population(&pool) == List<int32>::Cons(1, List<int32>::Nil);
    step(preserve(&pool), { member: first });
    have first.model == List<int32>::Cons(7, List<int32>::Nil);
    have count(ticket(&pool)) == 1;
    unfold(first);
    unfold(authority(ticket(&pool)));
    execute(); simp();
}
```

```expect
pass
```
