# The final implication check must not re-prove an already checked postcondition

The obsolete integer-only population is now an explicitly selected logical
resource model. Its scalar callback signature and exact-one claim remain.
Pointer-anchored population preservation is covered by
`authority_external_named_callback.md`.

```click resource_semantics=authority
resource Permit(x: int32) { field units: int32; }
contract Raw(permit: Permit(x)) for void(int32 x) {
    owns permit;
    ensures permit.units == old(permit.units);
}
contract Target(permit: Permit(x)) for void(int32 x) {
    owns permit;
    requires permit.units == 1;
    ensures permit.units == 1;
}
theorem lift(callback: void (*)(int32)) executes callback(int32 value) {
    requires Raw(callback);
    ensures Target(callback) as { permit: model } by { step(Raw(model)); simp(); }
}
```

```expect
pass
```
