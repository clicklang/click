# an unwritten element of a million-element array is zero at program entry

The elements an initializer leaves out are one run of zeros at program entry.
Such an element reads as exactly zero, so a claim that it holds anything else
is refused.

```c filename=an_unwritten_element_of_a_million_element_array_is_zero_at_program_entry.c
int32 buf[1000000] = {1, 2, 7};

int main(void) {
    return buf[500];
}
```

```click
verifying "an_unwritten_element_of_a_million_element_array_is_zero_at_program_entry.c";

int main() {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: left side evaluated to 0, right side evaluated to 1
```
