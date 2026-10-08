# Narrow scalar casts in contract expressions

The casts use the existing checked C conversion rules, including on the left
of a proposition and inside a historical observation.

```c filename=contract_narrow_scalar_casts.c
uint16 retain(uint16 x) { return x; }
```

```click
verifying "contract_narrow_scalar_casts.c";

theorem narrow_boundaries() {
    ensures (int8)(-128) == -128 by simp;
    ensures 127 == (int8)127 by simp;
    ensures (uint8)255 == 255 by simp;
    ensures (int16)(-32768) == -32768 by simp;
    ensures 32767 == (int16)32767 by simp;
    ensures (uint16)65521 == (uint16)65521 by simp;
    ensures (uint32)(uint16)65535 == 65535u32 by simp;
}

uint16 retain(uint16 x) {
    ensures result == old((uint16)(int32)x);
} by { execute(); simp(); }
```

```expect
pass
```
