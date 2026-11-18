# Unnamed bit-fields place members without entering the initializer

```c filename=fields.c

struct separated {
    unsigned char prefix;
    unsigned int : 3;
    unsigned int : 0;
    unsigned char suffix;
};

struct flags {
    unsigned int low : 3, : 2, high : 3;
    unsigned int : 0;
    unsigned int next : 8;
};

int answer(void) {
    struct separated a = { 2, 3 };
    struct flags b = { 1, 2, 3 };
    const unsigned char *bytes = (const unsigned char *)&b;
    return sizeof(a) == 5 && __builtin_offsetof(struct separated, suffix) == 4 &&
           a.prefix == 2 && a.suffix == 3 &&
           sizeof(b) == 8 && b.low == 1 && b.high == 2 && bytes[4] == 3;
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == 1; }
```

```expect
pass
```
