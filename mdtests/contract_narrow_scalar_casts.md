# Narrow scalar casts in contract expressions

The casts use the existing checked C conversion rules, including on the left
of a proposition and inside a historical observation.

```c filename=contract_narrow_scalar_casts.c
uint16 retain(uint16 x) { return x; }
```

```click
verifying "contract_narrow_scalar_casts.c";

theorem narrow_boundaries() {
    ensures (int8)(-128) == -128 by solve();
    ensures 127 == (int8)127 by solve();
    ensures (uint8)255 == 255 by solve();
    ensures (int16)(-32768) == -32768 by solve();
    ensures 32767 == (int16)32767 by solve();
    ensures (uint16)65521 == (uint16)65521 by solve();
    ensures (uint32)(uint16)65535 == 65535u32 by solve();
}

uint16 retain(uint16 x) {
    ensures result == old((uint16)(int32)x);
}
```

```expect
pass
```
