# Consuming and producing one place is spelled `owns`

`consumes p[0..1];` beside `produces p[0..1];` lends the cell to the call and
returns it, which is exactly what `owns p[0..1];` says. The language keeps
one spelling per form, so the pair is refused with the clause to write. A
pair whose place reads memory, such as `box->data[0..1]`, can name another
object at exit and stays a transformation
(`two_opaque_reallocating_calls_do_not_carry_an_unstated_value.md`).

```c filename=consumes_and_produces_one_place_is_owns.c
void set(int32 p[], int32 x) {
    p[0] = x;
}
```

```click
verifying "consumes_and_produces_one_place_is_owns.c";

void set(int32 p[], int32 x) {
    consumes p[0..1];
    produces p[0..1];
    ensures p[0] == x;
}
```

```expect
fail: `set` consumes and produces `p[0..1]`; write the one clause `owns p[0..1];`
```
