# Native byte-view casts in contracts

Byte views preserve allocation identity and offset. Arithmetic after the cast
counts bytes, while arithmetic before it uses the source element width.

```c filename=contract_byte_pointer_casts.c
uint32* next(uint32* p) { return p + 1; }
```

```click
verifying "contract_byte_pointer_casts.c";

uint32* next(uint32* p) {
    ensures (uint8*)result == old((uint8*)(p + 1));
    ensures (uint8*)result == (uint8*)p + 4;
} by { execute(); simp(); }
```

```expect
pass
```
