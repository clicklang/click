# Taking and casting the address of an unwritten word

```c filename=address.c
void f() { uint32 obj; obj = 0; }
```

```click
verifying "address.c";
void f() { ensures true; } by {
    step();
    have ((&obj) as (uint8 *)) == ((&obj) as (uint8 *)) by { known(); }
    step_until(function.exit);
}
```

```expect
pass
```
