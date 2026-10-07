# Pointer arithmetic through an aliased owner is not judged by the alias's range

`q[i]` forms `q + i`. The only range held is `owns p[1..n]`, and `p == q` is a
published offset equality between two parameters, not a structural one, so
the index of `q + i` relative to `p` is the residue `(q + i) - p`, which the
facts never bound. A range based in another object neither refutes nor bounds
the formation; the store's authority over `p[1..n]` is still established by
the resource algebra, which reads the alias.

```c filename=symbolic_write.c
void put(int32* p, int32* q, int32 i, int32 n) { q[i] = 7; }
```

```click
verifying "symbolic_write.c";

void put(int32* p, int32* q, int32 i, int32 n) {
    requires p == q;
    requires 1 <= i;
    requires i < n;
    owns p[1..n];
    ensures q[i] == 7;
} by { execute(); simp(); }
```

```expect
pass
```
