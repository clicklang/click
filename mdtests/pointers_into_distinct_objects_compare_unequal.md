# Pointers into distinct objects still compare unequal

The positive companion to
`a_one_past_the_end_pointer_is_not_compared_with_another_object.md`. Only the
one-past-end-against-start configuration is left to object placement. Two
objects' starts are distinct, a pointer inside one object is distinct from
the start of another, and a pointer compares equal to itself even one past
the end of its object.

```c filename=pointers_into_distinct_objects_compare_unequal.c
int32 starts(int32 x) { int32 a[2]; int32 b[2]; a[0] = 1; b[0] = 2; return a == b; }

int32 interior(int32 x) { int32 a[2]; int32 b[2]; a[0] = 1; b[0] = 2; return (a + 1) == b; }

int32 same_end(int32 x) { int32 a[2]; a[0] = 1; return (a + 2) == (a + 2); }
```

```click
verifying "pointers_into_distinct_objects_compare_unequal.c";

int32 starts(int32 x) {
    ensures result == 0;
} by { execute(); simp(); }

int32 interior(int32 x) {
    ensures result == 0;
} by { execute(); simp(); }

int32 same_end(int32 x) {
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
pass
```
