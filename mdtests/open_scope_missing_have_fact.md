# A missing fact inside an open scope is reported precisely

```c filename=open_fact.c
void touch(int32* p) { p[0] = 1; }
```

```click
resource cell(p: int32*) { owns p[0..1]; }
verifying "open_fact.c";
void touch(int32* p) {
    owns cell(p);
    ensures p[0] == 1;
} by {
    open(cell(p)) {
        have p[0] == 0 by simp;
        step();
    }
    execute(); simp();
}
```

```expect
fail: Requires p[0] == 0
```
