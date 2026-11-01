# A saved memory cell does not increment its index

Naming cell `INT32_MAX` requires no signed `INT32_MAX + 1` calculation.
The descriptor names one element at its computed address, like `memory(p[i])`.

```c filename=saved_max_index.c
void keep(int *p) {}
```

```click
import click::separation;
verifying "saved_max_index.c";
void keep(int32 *p) { ensures true; } by {
    have separate(memory(old(p)[2147483647]), memory(old(p)[0])) by {
        apply(separation::elements(old(p), 2147483647, 0)) using {};
    }
    step();
}
```

```expect
pass
```
