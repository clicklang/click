# string predicates need an import when the C program uses no string function

The negative twin of
[`a_string_function_call_brings_the_c_string_contracts.md`](a_string_function_call_brings_the_c_string_contracts.md).
This C program declares and calls no `<string.h>` function, so
`click::c::string` does not bring `click::cstr`, and the short path
`cstr::readable` is refused; the message names the import to add, or the
full path, which needs no import.

```c filename=string_predicates_need_an_import_without_a_string_function.c
int first(const unsigned char *text) {
    return text[0];
}
```

```click
verifying "string_predicates_need_an_import_without_a_string_function.c";

int32 first(const uint8* text) {
    requires cstr::readable(text);
    ensures 1 == 1 by { execute(); simp(); }
}
```

```expect
fail: `cstr::readable` names Click library module `click::cstr`, which this file does not import; add `import click::cstr;` or write `click::cstr::readable`
```
