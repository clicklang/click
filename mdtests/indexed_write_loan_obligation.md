# An indexed write proves its loan obligation by restriction

The implicit proof must expand to ordinary containment and separation steps.

```c filename=write_i_read_j.c
int32 write_i_read_j(int32 p[], int32 i, int32 j, int32 n) {
    p[i] = 9;
    return p[j];
}
```

```click
verifying "write_i_read_j.c";

int32 write_i_read_j(int32 p[], int32 i, int32 j, int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires i >= 0;
    requires i < n;
    requires j >= 0;
    requires j < n;
    consumes p[i..i + 1];
    views p[j..j + 1];
    requires separate(memory(p[i..i + 1]), memory(p[j..j + 1]));
    ensures keeps_j: result == old(p[j]);
}
```

```expect
pass
```
