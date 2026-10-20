# A file-scope string-pointer table is refused

A string literal's storage is modeled per function, so a pointer initializer
may name one only inside a function body. A function-scope `static` table
holds literals
([`string_get_size_unit_tables_are_static_string_pointer_tables.md`](string_get_size_unit_tables_are_static_string_pointer_tables.md)).
At file scope the same table is refused by name rather than with an unrelated
message.

```c filename=file_scope_table.c
static const char *const units_10[] = {
	"", "k", "M", "G", "T", "P", "E", "Z", "Y",
};

char first_letter(int i)
{
	return units_10[i][0];
}
```

```click
verifying "file_scope_table.c";

char first_letter(int32 i) {
    requires i == 1;
    ensures result == 107;
} by {
    execute();
    simp();
}
```

```expect
fail: file-scope pointer initializers do not support string literals yet
```
