# A borrowed byte composite with a quantified fact opens

A composite over byte cells states a quantified fact about them. A function
that borrows the composite can open it: the fact the opening publishes reads
each cell as a byte, as the kernel's own instantiation of the body does, both
for `uint8` cells with a `uint64` index and for `char` cells with an `int32`
index.

```c filename=a_borrowed_byte_composite_with_a_quantified_fact_opens.c
uint8 first_byte(uint8 p[], uint64 n) { return p[0]; }

char first_char(char p[], int n) { return p[0]; }
```

```click
resource nonzero_bytes(p: uint8*, n: uint64) {
    views p[0..n];
    fact forall (k: uint64) { 0u64 <= k and k < n implies p[k] != 0 };
}

resource nonzero_chars(p: char*, n: int32) {
    views p[0..n];
    fact forall (k: int32) { 0 <= k and k < n implies p[k] != '\0' };
}

verifying "a_borrowed_byte_composite_with_a_quantified_fact_opens.c";

uint8 first_byte(uint8 p[], uint64 n) {
    requires 0u64 < n;
    views nonzero_bytes(p, n);
    ensures true;
} by {
    open(nonzero_bytes(p, n)) {
        execute();
    }
}

char first_char(char p[], int32 n) {
    requires 0 < n;
    views nonzero_chars(p, n);
    ensures true;
} by {
    open(nonzero_chars(p, n)) {
        execute();
    }
}
```

```expect
pass
```
