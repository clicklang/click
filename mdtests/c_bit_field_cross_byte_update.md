# A field spanning bytes uses the same values as character access

```c filename=fields.c
struct fields {
    unsigned int low : 3;
    unsigned int number : 9;
    unsigned int high : 4;
};

int answer(void) {
    struct fields f;
    unsigned char *bytes = (unsigned char *)&f;
    bytes[0] = 0xfa;
    bytes[1] = 0xc0;
    f.number += 1;
    return f.low == 2 && f.number == 32 && f.high == 12 &&
           bytes[0] == 2 && bytes[1] == 0xc1;
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == 1; }
```

```expect
pass
```
