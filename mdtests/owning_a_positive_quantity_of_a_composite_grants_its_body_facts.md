# Owning a positive quantity of a composite grants its body facts

Where the quantity of an owned composite is known to be positive, at least one
instance of its body is held, so its body facts are available: here from a
`requires`, and for a plain `owns bundle(n)`, whose quantity is one.

```c filename=owning_a_positive_quantity.c
void probe_many(int32 amount, int32 n) {}
void probe_one(int32 n) {}
```

```click
abstract resource atom();
resource bundle(n: int32) {
    owns atom();
    fact n == 3;
}
verifying "owning_a_positive_quantity.c";
void probe_many(int32 amount, int32 n) {
    requires amount > 0;
    owns amount of bundle(n);
    ensures n == 3;
} by {
    execute();
}
void probe_one(int32 n) {
    owns bundle(n);
    ensures n == 3;
} by {
    execute();
}
```

```expect
pass
```
