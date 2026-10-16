# A typedef array parameter is adjusted to a pointer

C adjusts a parameter of array type to a pointer to its element, whether the
array is written in the declarator, `int values[3]`, or comes from a
typedef, `triple values` (C11 6.7.6.3p7). The C front end adjusts both, so a
head restating the declaration with an explicit array type matches either.

```c filename=main.c
typedef int triple[3];

void clear(triple values) {
    values[2] = 0;
}

int first(triple values) {
    return values[0];
}
```

```click
verifying "main.c";

void clear(int values[3]) {
    owns values[2];
    ensures values[2] == 0;
} by {
    execute();
    simp();
}

int first(int values[3]) {
    views values[0];
    ensures result == values[0];
} by {
    execute();
    simp();
}
```

```expect
pass
```
