# A proof mark names the state before a write

`mark` names the current frontier state, and a later `have` compares the
written cell with its value at that mark.

```c filename=proof_mark_before_write.c
int32 bump(int32* p) {
    p[0] = p[0] + 1;
    return 0;
}
```

```click
verifying "proof_mark_before_write.c";

int32 bump(int32* p) {
    owns p[0..1];
    requires p[0] < 2147483647;
    ensures p[0] == old(p[0]) + 1;
} by {
    mark before_write;
    step();
    have p[0] == at(before_write, p[0]) + 1 by simp;
    execute();
    simp();
}
```

```expect
pass
```
