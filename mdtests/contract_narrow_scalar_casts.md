# Narrow scalar casts in contract expressions

The casts use the existing checked C conversion rules, including on the left
of a proposition and inside a historical observation.

```c filename=contract_narrow_scalar_casts.c
uint16 retain(uint16 x) { return x; }
```

```click
verifying "contract_narrow_scalar_casts.c";

theorem narrow_boundaries() {
    ensures (-128) as int8 == -128 by solve();
    ensures 127 == 127 as int8 by solve();
    ensures 255 as uint8 == 255 by solve();
    ensures (-32768) as int16 == -32768 by solve();
    ensures 32767 == 32767 as int16 by solve();
    ensures 65521 as uint16 == 65521 as uint16 by solve();
    ensures 65535 as uint16 as uint32 == 65535u32 by solve();
}

uint16 retain(uint16 x) {
    ensures result == old(x as int32 as uint16);
}
```

```expect
pass
```
