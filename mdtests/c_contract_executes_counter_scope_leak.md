# Execution target resource names do not escape their proof block

```c filename=counter.c
int32 invoke(int32 (*callback)()) { return callback(); }
```

```click
resource Counter() { field revision: int32; field tag: int32; }
contract int32 Exact() {
    owns cell: Counter();
    requires cell.revision < 2147483647;
    ensures cell.revision == old(cell.revision) + 1;
    ensures result == 0;
}
contract int32 Progress() {
    owns cell: Counter();
    requires cell.revision < 2147483647;
    ensures cell.revision > old(cell.revision);
    ensures result == 0;
}
theorem lift(callback: int32 (*)()) executes callback() {
    requires Exact(callback);
    ensures Progress(callback) as { cell: k } by {
        step(Exact, { cell: k });
        have k.revision == old(k.revision) + 1 by assumption();
        apply(int32_increment_strictly_increases(old(k.revision), 2147483647));
        simp();
    }
}
theorem outside(callback: int32 (*)()) {
    requires Exact(callback);
    ensures 1 == 1 by step(Exact, { cell: cell });
}
verifying "counter.c";
int32 invoke(int32 (*callback)()) {
    requires Exact(callback);
    owns first: Counter();
    owns second: Counter();
    requires first.revision < 2147483647;
    ensures first.revision > old(first.revision);
    ensures second.revision == old(second.revision);
    ensures second.tag == old(second.tag);
    ensures result == 0;
} by {
    apply(lift(callback));
    step(Progress, { cell: first });
    execute();
    simp();
}
```

```expect
fail: unknown resource instance `cell`
```
