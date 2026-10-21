# A program-entry string literal provides its C-string view

The program entry holds its literals as views installed at startup, not as
owned bytes. A literal's C-string view comes from its bytes alone, so
`strlen("abc")` in `main` takes it the same way an ordinary function does
([`a_string_literal_provides_its_c_string_view.md`](a_string_literal_provides_its_c_string_view.md)).

```c filename=entry_literal.c
unsigned long strlen(const char *s);

int main(void)
{
	return (int)strlen("abc");
}
```

```click
verifying "entry_literal.c";

int main() {
    ensures result == 3;
} by {
    execute();
    simp();
}
```

```expect
pass
```
