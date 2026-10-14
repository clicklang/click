# Source and target resource parameter names are independent

The theorem selects the target contract's arbitrary counter instance. The
caller applies the resulting contract to one counter and frames a second.

```c filename=counter.c
int32 invoke(int32 (*callback)()) { return callback(); }
```

```click
import click::machine_integer;

resource Counter() { field revision: int32; field tag: int32; }
contract int32 Exact() {
    owns cell: Counter();
    requires cell.revision < 2147483647;
    ensures cell.revision == old(cell.revision) + 1;
    ensures result == 0;
}
contract int32 Progress() {
    owns counter: Counter();
    requires counter.revision < 2147483647;
    ensures counter.revision > old(counter.revision);
    ensures result == 0;
}
theorem lift(callback: int32 (*)()) executes callback() {
    requires Exact(callback);
    ensures Progress(callback) as { counter: k } by {
        step(Exact, { cell: k });
        have k.revision == old(k.revision) + 1 by assumption();
        apply(int32_increment_strictly_increases(old(k.revision), 2147483647));
        simp();
    }
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
    step(Progress, { counter: first });
    execute();
    simp();
}
```

```expect
pass
```

