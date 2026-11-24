# A byte function reads a string literal as unsigned bytes

Plain `char` is signed on this target, so a string literal is an array of
signed characters. A pure function's `uint8[]` parameter reads its argument
as unsigned bytes, as a predicate's does, so the literal's byte `0xe9` is
`233u8`, and a `List<uint8>` built from it is the list a proof writes.

```c filename=a_byte_function_reads_a_string_literal_as_unsigned_bytes.c
int first(const char *s);

int run(void)
{
    return first("\xe9!");
}
```

```click
verifying "a_byte_function_reads_a_string_literal_as_unsigned_bytes.c";

function first_list(s: uint8[]) -> List<uint8> {
    List<uint8>::Cons(s[0u64], List<uint8>::Nil)
}

extern int32 first(const uint8* s) {
    let n: uint64;
    views click::c::string::cstr_at(s, n);
    ensures true;
}

int32 run() {
    ensures true;
} by {
    step();
    have first_list("a_byte_function_reads_a_string_literal_as_unsigned_bytes.c"::run.string_literal(0)) == List::Cons(233u8, List::Nil) by {
        unfold(first_list("a_byte_function_reads_a_string_literal_as_unsigned_bytes.c"::run.string_literal(0)));
        close();
    }
    step();
}
```

```expect
pass
```
