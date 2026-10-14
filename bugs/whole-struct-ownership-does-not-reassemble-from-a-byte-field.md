# Whole-struct ownership does not reassemble from a byte field

Soundness: incomplete. The verifier refuses a valid call; it never accepts a
false claim. `owns *p` and the complete list of `p`'s fields describe the
same bytes, and only the direction from fields to `*p` is refused.

`owns *p` for a struct is documented as the object's complete storage, and
a function that holds `*p` lends any one field to a callee. The opposite
direction fails for a byte field: a caller that holds
every field of `*p` by name cannot call a function that takes `owns *p`
when one field is narrower than its slot's `int32` cells. Two `int` fields,
and two `uint64` fields, reassemble; `{ int a; char c; }` does not. The
whole object is held as `int32` cells and the `char` field as byte cells,
and the coverage check does not combine the bytes into the object's cell.

Reproduced on master `943b72c`:

```c
struct mixed { int a; char c; };

int set_c(struct mixed *p) { p->c = 1; return 0; }
int mixed_fields(struct mixed *p) { set_c(p); return p->a; }
```

```click
int32 set_c(struct mixed* p) { owns *p; ensures result == 0; }
int32 mixed_fields(struct mixed* p) {
    requires aligned(p, 4);
    owns p->a;
    owns p->c;
}
```

`mixed_fields` fails with "held `owns p->a` does not cover `*p`"
(`8 <= 4` is false): the byte cells of `c` are not counted.

Acceptance: an mdtest with the caller above passes; the callee's
`*p` is consumed piecewise from the fields and returned to them; a caller
missing one field is still refused naming the missing field; no new trusted
rule beyond the existing byte view of a cell.
