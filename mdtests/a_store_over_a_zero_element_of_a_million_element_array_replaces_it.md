# a store over a zero element of a million-element array replaces it

A tentative definition's elements are one run of zeros at program entry. A
store into one element replaces that element alone, so reading it back yields
the stored value and a claim that it is still zero is refused.

```c filename=a_store_over_a_zero_element_of_a_million_element_array_replaces_it.c
int32 buf[1000000];

int main(void) {
    buf[5] = 9;
    return buf[5];
}
```

```click
verifying "a_store_over_a_zero_element_of_a_million_element_array_replaces_it.c";

int main() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: left side evaluated to 9, right side evaluated to 0
```
