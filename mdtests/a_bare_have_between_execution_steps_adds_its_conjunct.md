# A bare `have` between execution steps adds its conjunct

`have P;` proves an intermediate fact at the current execution frontier.
The implicit tail then runs the remaining C and closes the function claims.

```c filename=a_bare_have_between_execution_steps_adds_its_conjunct.c
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    a[i] = 1;
}
```

```click
verifying "a_bare_have_between_execution_steps_adds_its_conjunct.c";

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
    have m != i;
}
```

```expect
pass
```
