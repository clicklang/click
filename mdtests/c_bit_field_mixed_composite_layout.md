# Layout queries include arrays, pointers, and embedded members

```c filename=fields.c
struct inner { unsigned short value; };

struct fields {
    unsigned char kind;
    unsigned int flags : 5;
    struct inner embedded;
    unsigned int table[2];
    void *pointer;
};

int answer(void) {
    return sizeof(struct fields) == 24 &&
           __builtin_offsetof(struct fields, embedded) == 2 &&
           __builtin_offsetof(struct fields, table) == 4 &&
           __builtin_offsetof(struct fields, pointer) == 16;
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == 1; }
```

```expect
pass
```
