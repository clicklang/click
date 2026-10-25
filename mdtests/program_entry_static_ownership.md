# Program startup owns initialized static storage

```c filename=main.c
unsigned int counter = 7;
unsigned int bump(unsigned int *p) { *p += 1; return *p; }
int main(void) { bump(&counter); return bump(&counter); }
```

```click
verifying "main.c";
unsigned int bump(unsigned int *p) {
    owns p[0..1];
    ensures to_integer(p[0]) == to_integer(old(p[0]) + 1u32);
    ensures result == p[0];
    ensures to_integer(result) == to_integer(old(p[0]) + 1u32);
}
int main() {
    ensures result == 9;
} by {
    step();
    mark first;
    have counter == 8u32;
    step_until(function.exit);
    have to_integer(result) == to_integer(at(first, counter) + 1u32);
    rewrite(to_integer(result) == to_integer(at(first, counter) + 1u32));
    rewrite(at(first, counter) == 8u32);
    solve();
}
```

```expect
pass
```
