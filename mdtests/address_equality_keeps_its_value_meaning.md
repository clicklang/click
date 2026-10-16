# A C pointer comparison still decides addresses

A C pointer comparison states that the two addresses are equal. That still
decides later comparisons and results, and a pointer equality stated by the
contract still decides the comparison. Access through the pointer that
carries the authority is unaffected: only reading through the other pointer
on the strength of the comparison is refused
(`address_equality_does_not_grant_access_to_a_one_past_pointer.md`).

```c filename=compare.c
int32 same(int32* q, int32* p) { return q == p; }
int32 twice(int32* q, int32* p) { if (q == p) { return q == p; } return 1; }
int32 through_carrier(int32* q, int32* p) { if (q == p) { return *p; } return 0; }
```

```click
verifying "compare.c";
int32 same(int32* q, int32* p) {
    ensures result == 1 implies address(q) == address(p);
    ensures address(q) == address(p) implies result == 1;
} by { execute(); simp(); }
int32 twice(int32* q, int32* p) {
    ensures result == 1;
} by { execute(); simp(); }
int32 through_carrier(int32* q, int32* p) {
    views p[0..1];
    requires q == p;
    ensures result == p[0];
} by { execute(); simp(); }
```

```expect
pass
```
