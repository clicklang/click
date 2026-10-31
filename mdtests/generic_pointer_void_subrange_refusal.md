# A void pointer has no element interval

```click
import click::separation;
theorem no_elements(p: void*) {
    ensures true by {
        apply(separation::subrange(p, 0, 1, 0, 1)) using {
            0 <= 0; 0 <= 1; 1 <= 1;
        };
    }
}
```

```expect
fail: expected a typed pointer argument
```
