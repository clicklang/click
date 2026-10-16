# Owning zero of a composite grants no body fact

`amount of bundle(n)` holds `amount` instances of `bundle`'s body, so a body
fact describes an instance only where `amount > 0` is known. With
`amount == 0` there is no instance, and `n == 3` is not available: otherwise
`caller` would pass `probe(0, 5)` and receive `5 == 3`. The same holds for a
symbolic `amount` the proof does not know to be positive.

```c filename=owning_zero_of_a_composite.c
void probe(int32 amount, int32 n) {}
int32 caller() {
    probe(0, 5);
    return 0;
}
```

```click
abstract resource atom();
resource bundle(n: int32) {
    owns atom();
    fact n == 3;
}
verifying "owning_zero_of_a_composite.c";
void probe(int32 amount, int32 n) {
    requires amount == 0;
    owns amount of bundle(n);
    ensures n == 3;
} by {
    execute();
}
int32 caller() {
    ensures 1 == 0;
} by auto();
```

```expect
fail: `probe.ensures_0`
```
