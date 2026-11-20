# An output cannot borrow from a different input that does not cover it

```c filename=first.c
int *first(int *left, int *right) { return left; }
```

```click
verifying "first.c";

int32* first(int32* left, int32* right) {
    views *left;
    views *right as right_input;
    produces view(*left) from right_input;
    ensures result == left;
}
```

```expect
fail: The selected input `views right[0]` does not establish coverage of `views left[0]`
```
