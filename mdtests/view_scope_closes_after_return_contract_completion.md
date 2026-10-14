# A viewed scope closes after the return contract has been established

```c filename=completed_scope.c
void repair(void) { }
void finish(int32* p) { repair(); }
```

```click
verifying "completed_scope.c";
resource viewed(p: int32*) { views p[0..1]; }
resource marker() { field value: int32; }
void repair() {
    produces tag: marker();
    ensures tag.value == 1;
} by {
    execute();
    let tag = fold(marker(), { value: 1 });
    simp();
}
void finish(int32* p) {
    views viewed(p);
    produces tag: marker();
    ensures tag.value == 1;
} by {
    open(viewed(p)) {
        let { tag: tag } = step(repair(), {});
        execute(); simp();
    }
}
```

```expect
pass
```
