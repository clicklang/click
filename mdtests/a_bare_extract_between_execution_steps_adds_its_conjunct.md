# A bare `extract` between execution steps adds its conjunct

`extract(P)` written between execution steps adds `P` exactly as
`have P by { extract(P); }` does, as it already did after execution. The
execution frontier used to decline a bare `extract`, so the same tactic was
accepted after `execute()` and refused before it.

```c filename=a_bare_extract_between_execution_steps_adds_its_conjunct.c
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    a[i] = 1;
}
```

```click
verifying "a_bare_extract_between_execution_steps_adds_its_conjunct.c";

void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires m != i and 0 <= n;
    requires n <= 1073741823;
    owns a[0..n];
    ensures a[m] == old(a[m]);
} by {
    mark entry;
    extract(m != i);
    execute();
    simp();
}
```

```expect
pass
```
