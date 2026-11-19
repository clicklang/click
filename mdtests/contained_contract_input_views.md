# A contract can view a range and a contained slice

```c filename=contained_contract_input_views.c
int first(const int *p) { return p[0]; }
int read(const int *p) { return first(p); }
```

```click
verifying "contained_contract_input_views.c";
int32 first(const int32 *p) {
    views p[0..1];
    ensures result == p[0];
}

int32 read(const int32 *p) {
    views p[0..2];
    views p[0..1];
    ensures result == p[0];
}
```

```expect
pass
```
