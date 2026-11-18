# A one-past row pointer cannot designate a row

```c filename=matrix.c
int read_past_matrix(void) {
    int matrix[2][3] = {{11, 12, 13}, {21, 22, 23}};
    int (*row)[3] = &matrix[1];
    ++row;
    return row[0][0];
}
```

```click
verifying "matrix.c";
int32 read_past_matrix() { ensures result == result; }
```

```expect
fail: outside the subobject
```
