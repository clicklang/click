# A negative `int32` fact prints as its unsigned bit pattern

Soundness: not soundness. Only the printed proof context is wrong; the fact
itself holds the right value, and no claim is accepted or refused because of
the printing.

A failing claim's proof context prints an `int32` fact about a negative
constant with the constant's 32-bit pattern read as unsigned. A diagnostic
must print a value in its own type: `-56` as an `int32` is `-56`, never
`4294967240`.

Reproduced on master `89981b0`:

```c filename=a.c
int minus(void) { return -56; }
int caller(void) { return minus(); }
```

```click
verifying "a.c";
int minus() { ensures result == -56 by auto; }
int caller() { ensures result == 200 by auto; }
```

`click verify` refuses `caller` (correctly), but its proof context reads

```text
pure facts: [int32 =(value A, 4294967240) is true]
```

where the fact recorded from `minus`'s contract is `A == -56`. The same
printing appears for a signed `char` read through a converted pointer (for
example `mdtests/a_false_claim_about_a_byte_read_through_a_converted_char_pointer_is_refused.md`,
whose callee result `int8(200)` prints as `4294967240`).

The intended regression is an mdtest with the source above whose `expect`
block names the fact as `int32 =(value A, -56)`.

Acceptance criteria:

- The reproduction's proof context prints `-56`, not `4294967240`.
- Unsigned `uint32` facts still print their unsigned values.
- The regression mdtest above passes under the default target.
