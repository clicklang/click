# A returned narrow load has its type range

The loaded-value form of
`mdtests/a_returned_narrow_parameter_has_its_type_range.md`: `return *p;`
through a `uint8*` returns a value in `[0, 255]`. The read of `*p` files the
loaded value's range where the value is produced.

```c filename=a_returned_narrow_load_has_its_type_range.c
int32 via_load(uint8* p) {
    return *p;
}
```

```click
verifying "a_returned_narrow_load_has_its_type_range.c";

int32 via_load(uint8* p) {
    views p[0..1];
    ensures result >= 0;
    ensures result <= 255;
} by { execute(); simp(); }
```

```expect
pass
```
