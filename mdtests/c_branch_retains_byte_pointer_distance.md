# A checked C branch retains the element width of a pointer distance

The branch condition subtracts two byte pointers. Its proof form refers to
the pointers recorded at the statement entry and uses the same element width.

```c filename=prefix.c
int prefix_available(const unsigned char * const input_pointer, const unsigned char * const input_end)
{
    const unsigned char *first_sequence = input_pointer;
    if ((input_end - first_sequence) < 6)
    {
        return 0;
    }
    return 1;
}
```

```click
verifying "prefix.c";

int prefix_available(const uint8* input_pointer, const uint8* input_end) {
    views input_pointer[0..12];
    requires input_end == input_pointer + 12;
    requires same_object(input_end, input_pointer);
    requires defined(input_end - input_pointer);
    ensures result == 0 or result == 1;
}
```

```expect
pass
```
