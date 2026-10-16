# A function head writes array typedef names

A parameter whose C type is a scalar array typedef name of the verified
source is written with that name: `triple values` stands for `int values[3]`,
which C passes as a pointer to the first element, and the alias's length
bounds the bytes the head declares, as a written length does. An alias of a
`const` element type keeps it.

```c filename=main.c
typedef int triple[3];
typedef const unsigned char digest[4];

int first(triple values) {
    return values[0];
}

void clear(triple values) {
    values[2] = 0;
}

unsigned char last_byte(digest bytes) {
    return bytes[3];
}
```

```click
verifying "main.c";

int first(triple values) {
    views values[0];
    ensures result == values[0];
} by {
    execute();
    simp();
}

void clear(triple values) {
    owns values[2];
    ensures values[2] == 0;
} by {
    execute();
    simp();
}

unsigned char last_byte(digest bytes) {
    views bytes[3];
    ensures result == bytes[3];
} by {
    execute();
    simp();
}
```

```expect
pass
```
