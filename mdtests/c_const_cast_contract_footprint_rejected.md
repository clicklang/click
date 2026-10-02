# A contract cannot own const storage passed through a const parameter

A callee that casts its `const` parameter and writes through it needs an
owned footprint. A caller cannot supply one for a const table: no owned
footprint may cover read-only storage.

```c filename=c_const_cast_contract_footprint_rejected.c
int overwrite(const int *q) {
    int *p = (int *)q;
    *p = 7;
    return 0;
}

const int table[2] = {1, 2};

int32 run(void) {
    overwrite(table);
    return table[0];
}
```

```click
verifying "c_const_cast_contract_footprint_rejected.c";

int32 overwrite(const int32* q) {
    owns q[0..1];
    ensures q[0] == 7 by auto;
}

int32 run() {
    owns table[0..2];
    ensures result == 7 by auto;
}
```

```expect
fail: mutable footprint covers read-only storage `global:table`
```
