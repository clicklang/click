# a written element of a million-element array is not another value at program entry

The unwritten elements of an initialized array are one run of zeros at program
entry, and the elements its initializer writes are stored over that run. A
written element reads as exactly its initializer, so a claim that it holds
anything else is refused.

```c filename=a_written_element_of_a_million_element_array_is_not_another_value_at_program_entry.c
int32 buf[1000000] = {1, 2, 7};

int main(void) {
    return buf[2];
}
```

```click
verifying "a_written_element_of_a_million_element_array_is_not_another_value_at_program_entry.c";

int main() {
    ensures result == 8;
} by {
    execute();
    simp();
}
```

```expect
fail: left side evaluated to 7, right side evaluated to 8
```
