# reads of one kind at one address stay equal

A load term carries the kind of its read, and two reads of one address name
one value exactly when they agree on it. These are the reads that do: the
same signed read twice, a read through an alias of the same type, an
unsigned read compared with a callee's promise about the same unsigned read,
a contract that names the body's own read, and an `int32` and a `uint32` read
of one word, which keep its bit pattern and differ only in how it is read.

`a_signed_and_an_unsigned_byte_read_are_two_values.md`,
`a_byte_read_is_not_the_int32_read_at_its_address.md` and
`a_callee_unsigned_read_is_not_the_callers_signed_read.md` are the reads that
do not agree.

```c filename=reads_of_one_kind_at_one_address_stay_equal.c
#include <stdint.h>

int get_u(unsigned char* u, int i) {
    return u[i];
}

int same_signed_twice(signed char* s, int i) {
    int a;
    int b;
    a = s[i];
    b = s[i];
    return a == b;
}

int same_through_alias(signed char* s, int i) {
    signed char* t;
    int a;
    int b;
    t = s;
    a = s[i];
    b = t[i];
    return a == b;
}

int unsigned_across_call(unsigned char* u, int i) {
    int a;
    int b;
    a = u[i];
    b = get_u(u, i);
    return a == b;
}

int returns_own_read(unsigned char* u, int i) {
    return u[i];
}

int int32_bits_as_uint32(int32_t* q, int i) {
    uint32_t* r;
    r = (uint32_t*)(void*) q;
    return (uint32_t) q[i] == r[i];
}
```

```click
verifying "reads_of_one_kind_at_one_address_stay_equal.c";

int get_u(unsigned char* u, int i) {
    requires i >= 0;
    requires i < 4;
    views u[0..4];
    ensures result == u[i];
} by {
    execute();
    simp();
}

int same_signed_twice(signed char* s, int i) {
    requires i >= 0;
    requires i < 4;
    views s[0..4];
    ensures result == 1;
} by {
    execute();
    simp();
}

int same_through_alias(signed char* s, int i) {
    requires i >= 0;
    requires i < 4;
    views s[0..4];
    ensures result == 1;
} by {
    execute();
    simp();
}

int unsigned_across_call(unsigned char* u, int i) {
    requires i >= 0;
    requires i < 4;
    views u[0..4];
    ensures result == 1;
} by {
    execute();
    simp();
}

int returns_own_read(unsigned char* u, int i) {
    requires i >= 0;
    requires i < 4;
    views u[0..4];
    ensures result == u[i];
} by {
    execute();
    simp();
}

int int32_bits_as_uint32(int32_t* q, int i) {
    requires i >= 0;
    requires i < 4;
    views q[0..4];
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
