# Expression updates preserve the consumed value and the stored value

```c filename=updates.c
int old_value(void) { int n = 5; return n++; }
int new_value(void) { int n = 5; return ++n; }
unsigned long exit_decrement(void) {
    unsigned long n = 0;
    while (n--) { }
    return n;
}
int continue_condition(void) {
    int n = 3;
    int count = 0;
    do { count++; continue; } while (--n);
    return count;
}
unsigned int read_pair(const unsigned char *p) {
    unsigned int sum = 0;
    sum += *p++;
    sum += *p++;
    return sum;
}
```

```click
verifying "updates.c";
int32 old_value() { ensures result == 5; } by { execute(); simp(); }
int32 new_value() { ensures result == 6; } by { execute(); simp(); }
uint64 exit_decrement() { ensures result == 18446744073709551615u64; } by { execute(); simp(); }
int32 continue_condition() { ensures result == 3; } by { execute(); simp(); }
uint32 read_pair(const uint8* p) {
    views p[0..2];
    ensures result == (uint32)p[0] + (uint32)p[1];
    ensures p[0] == old(p[0]);
    ensures p[1] == old(p[1]);
} by { execute(); simp(); }
```

```expect
pass
```
