# a callee unsigned read is not the caller's signed read

`get_u` promises to return `u[i]`, an unsigned byte read. The caller compares
that with its own `s[i]`, a signed read of the same byte, and claims they are
equal. They differ for every byte of `0x80` or more.

The claim was **provable**: the callee's postcondition, instantiated at the
call, named the same load term as the caller's read of the other kind. A load
term now carries its read's kind, so the reads are two terms on both sides of
the call boundary. `reads_of_one_kind_at_one_address_stay_equal.md` keeps the
same claim provable when both reads are unsigned.

```c filename=a_callee_unsigned_read_is_not_the_callers_signed_read.c
int get_u(unsigned char* u, int i) {
    return u[i];
}

int compare(signed char* s, int i) {
    unsigned char* u;
    int a;
    int b;
    u = (unsigned char*)(void*) s;
    a = s[i];
    b = get_u(u, i);
    return a == b;
}
```

```click
verifying "a_callee_unsigned_read_is_not_the_callers_signed_read.c";

int get_u(unsigned char* u, int i) {
    requires i >= 0;
    requires i < 4;
    views u[0..4];
    ensures result == u[i];
} by {
    execute();
    simp();
}

int compare(signed char* s, int i) {
    requires i >= 0;
    requires i < 4;
    views s[0..4];
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: `ensures result == 1` failed for `compare.ensures_0`
```
