# A claim that cannot lower is refused with its own cause, ahead of a claim that holds

`preserve` states two claims. The first holds: nothing writes `member`. The
second cannot be lowered: `count(...)` of `ticket(pool + 1)` needs owning
authority for that population, which the function does not hold. The
implicit tail closes the proposition claims as one group, and a claim whose
goal cannot be stated never closes, so the refusal is that claim and its
lowering error. The first claim, which holds, is not reported as an unclosed
goal.

```c filename=helper.c
void preserve(int32* pool) {}
int32 run() { int32 pool = 0; preserve(&pool); return 0; }
```

```click
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "helper.c";
void preserve(int32* pool) {
    owns authority(ticket(pool));
    owns member: ticket(pool);
    ensures member.serial == old(member.serial);
    ensures count(ticket(pool + 1)) >= 0;
}
```

```expect
fail: every pending claim: `ensures to_integer(count(ticket((pool + 1)))) >= 0` failed for `preserve.ensures_1` path 0: could not lower the claim goal
```
