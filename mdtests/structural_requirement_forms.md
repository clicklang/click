# Structural requirement forms

Each supported structural requirement, and the `views` and `consumes` memory
clauses, is accepted on a function contract.

```c filename=structural_requirement_forms.c
int32 structural_requirements(int32 p[], int32 n, int32 dst[], int32 src[], int32* begin, int32* end, int32 x) {
    return 0;
}

int32 view_first(int32 p[]) {
    return p[0];
}

int32 consume_first(int32 p[]) {
    p[0] = 0;
    return 0;
}
```

```click
verifying "structural_requirement_forms.c";

int32 structural_requirements(int32 p[], int32 n, int32 dst[], int32 src[], int32* begin, int32* end, int32 x) {
    requires n >= 0;
    requires viewable(p[0..n]);
    requires viewable((p + 1)[0..1]);
    requires separate(memory(dst[0..n]), memory(src[0..n]));
    requires same_object(begin, end);
    requires defined(x + 1);
    ensures result == 0 by auto();
}

int32 view_first(int32 p[]) {
    views p[0..1];
    ensures result == p[0] by auto();
}

int32 consume_first(int32 p[]) {
    consumes p[0..1];
    ensures result == 0 by auto();
}
```

```expect
pass
```
