# Returning ownership does not promise field preservation

The caller cannot infer a field guarantee omitted from the callback contract.

```c filename=invoke.c
int32 invoke(int32 (*callback)()) { return callback(); }
```

```click
verifying "invoke.c";
resource marker() { field revision: int32; }
contract int32 Touch() { owns cell: marker(); }

int32 invoke(int32 (*callback)()) {
    requires Touch(callback);
    owns first: marker();
    ensures first.revision == old(first.revision);
} by { step(Touch, { cell: first }); execute(); simp(); }
```

```expect
fail: unclosed goal: first.revision == old(first.revision)
```
