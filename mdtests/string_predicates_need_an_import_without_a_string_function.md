# string predicates need an import when the C program uses no string function

The negative twin of
[`a_string_function_call_brings_the_c_string_contracts.md`](a_string_function_call_brings_the_c_string_contracts.md).
This C program declares and calls no `<string.h>` function, so
`click::c::string` and the `click::cstr` predicates its contracts use are
not visible, and the message names the import to add.

```c filename=string_predicates_need_an_import_without_a_string_function.c
int first(const unsigned char *text) {
    return text[0];
}
```

```click
verifying "string_predicates_need_an_import_without_a_string_function.c";

int32 first(const uint8* text) {
    requires cstr_readable(text);
    ensures 1 == 1 by { execute(); simp(); }
}
```

```expect
fail: unknown predicate `cstr_readable` in requires clause in `first`; it is declared in Click library module `click::cstr`, so add `import click::cstr;`
```
