# A field of a scalar quantified variable gets a lowering message

Soundness: sound. The claim is refused; only its diagnostic is unusable.

A proposition that reads a field of a quantified variable of a scalar type,
such as `k.n` inside `forall (k: int32) { ... }`, is refused with a message
about kernel lowering instead of one naming the field read:

```c filename=scalar_field.c
void f(int32* p) { }
```

```click
verifying "scalar_field.c";

void f(int32* p) {
    requires true;
} by {
    have forall (k: int32) { k.n == 5 } by { simp(); }
    execute();
    simp();
}
```

```text
proof error:
  could not lower `have` proposition
  the kernel lowering produced 0 paths, not one
```

The message names neither `k`, its type nor the field `n`, and "0 paths"
describes the lowering, not the proposition. The read should be refused
where the proposition is read, saying that `k` is an `int32`, which has no
field `n`.

## Acceptance criteria

- `k.n` on a quantified `int32` `k` is refused with a message naming `k`,
  its type `int32` and the field `n`.
- `mdtests/a_quantified_variable_hides_a_value_binder_of_its_name.md`, which
  expects the current message because its quantified `s` hides a value
  binder with the field `n`, expects the new one.
- A regression keeps the pattern above: a field read on a scalar quantified
  variable inside a `have`.
