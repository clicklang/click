# Contract clause forms

This checks the requirement, resource, guarantee, label and proof-clause forms
that the contracts concept page shows, each on a small function.

```c filename=contract_clause_forms.c
int32 increment(int32 x) {
    return x + 1;
}

int32 labeled_increment(int32 x) {
    return x + 1;
}

int32 decrement(int32 x) {
    return x - 1;
}

int32 copy_first(int32 p[]) {
    p[1] = p[0];
    return p[1];
}

int32 clear(int32 x) {
    return 0;
}
```

```click
verifying "contract_clause_forms.c";

int32 increment(int32 x) {
    requires x >= 0;
    requires x < 2147483647;
    ensures result == x + 1 by auto;
    ensures result > x by auto;
}

int32 labeled_increment(int32 x) {
    requires x < 2147483647;
    ensures incremented: result == x + 1 by auto;
}

int32 decrement(int32 x) {
    requires x > 0;
    ensures result == x - 1 by auto;
}

int32 copy_first(int32 p[]) {
    views p[0..1];
    consumes p[1..2];
    ensures result == p[0] by auto;
}

int32 clear(int32 x) {
    requires x == 0;
    ensures result == 0 by auto;
    ensures result == x by { execute(); simp(); }
}
```

```expect
pass
```
