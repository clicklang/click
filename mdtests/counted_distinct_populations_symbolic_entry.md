# Distinct population counts need no invented bound on their sum

Individual counts may fit even when their sum does not. A proof that does not
observe the sum must not assume that adding them cannot overflow.

```c filename=counted_distinct_populations_symbolic_entry.c
int identity(void *p, void *q, int n) { return n; }
```

```click resource_semantics=authority
verifying "counted_distinct_populations_symbolic_entry.c";
authorized abstract resource ticket(p: void*);
int32 identity(void* p, void* q, int32 n) {
    owns authority(ticket(p));
    owns authority(ticket(q));
    owns ticket(p);
    owns ticket(q);
    requires p != q;
    requires count(ticket(p)) == n;
    requires count(ticket(q)) == 1;
    requires n >= 1;
    ensures result == n;
} by { execute(); simp(); }
```

```expect
pass
```
