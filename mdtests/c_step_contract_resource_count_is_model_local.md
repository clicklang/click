# A different resource model cannot evaluate its postcondition in the input ledger

The alternative transition returns B, not A, and records zero remaining A in
its selected logical model. Its conditional postcondition does not promise
result == 1 merely because the selected Keep model retains A.
The integer-only global population has been retired; the original C is unchanged.

```c filename=joint.c
int32 invoke(int32 (*callback)(int32), int32 x) { return callback(x); }
```

```click
resource A(x: int32) {}
resource B(x: int32) {}
resource Ledger() { field remaining: int32; }
contract Keep(model: Ledger()) for int32(int32 x) {
    owns model;
    owns A(x);
    ensures model.remaining == old(model.remaining);
    ensures result == 0;
}
contract Alternative(model: Ledger()) for int32(int32 x) {
    owns model;
    consumes A(x);
    produces B(x);
    ensures model.remaining == 0;
    ensures model.remaining == 1 implies result == 1;
}
verifying "joint.c";
int32 invoke(int32 (*callback)(int32), int32 x) {
    requires Keep(callback);
    requires Alternative(callback);
    owns model: Ledger();
    owns A(x);
    requires model.remaining == 1;
    ensures result == 1;
} by { step(Keep(model)); execute(); simp(); }
```

```expect
fail: unclosed goal
```
