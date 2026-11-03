# An exact-address owner is selected beside a symbolic prefix

The offset call consumes and returns the selected cell. The unrelated prefix
remains owned; selecting its tentative covering interval would refuse the call.

```c filename=exact_address_owner_beside_symbolic_prefix.c
void wr(int32* p) {
    *p = 1;
}

void caller(int32* x, int32 i, int32 j) {
    wr(x + j);
}
```

```click
verifying "exact_address_owner_beside_symbolic_prefix.c";

void wr(int32* p) {
    owns p[0..1];
    ensures p[0] == 1;
}

void caller(int32* x, int32 i, int32 j) {
    requires 0 <= i;
    requires i < 3;
    requires 0 <= j;
    requires to_integer(i + 1) <= to_integer(j);
    requires j < 4;
    owns x[0..(i + 1)];
    owns x[j..(j + 1)];
    ensures x[j] == 1;
}
```

```expect
pass
```
