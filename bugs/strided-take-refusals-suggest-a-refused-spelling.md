# Strided `take` refusals suggest a refused spelling

Soundness: not soundness. Nothing is accepted that should not be; the
refusals below are of ranges that do name the clause's element, and the
accepted spelling verifies. The defect is that the refusals mislead: one
says the range "is not one element" when it is exactly one, and the other
tells the user to write a spelling that is itself refused.

The violated invariant: a refusal's hint names a spelling the same tactic
accepts, and a refusal reason is true. [Taking a
range](../docs/reference/tactics/index.md#taking-a-range) accepts a strided
element only as `data[i * s + a..i * s + b]`, index first. For the clause
`owns data[2 * k..2 * k + 2];`:

- `take(data[index * 2..index * 2 + 2])` verifies.
- `take(data[2 * index..2 * index + 2])`, the clause's own factor order, is
  refused with "the range is not one element of the iterated ownership
  fact". It is one element; only its spelling is outside the documented form.
- `take(data[index + index..index + index + 2])` is refused with "write the
  element as `base[2 * index + 0..]`, the clause's own shape". Following that
  hint, `take(data[2 * index + 0..2 * index + 2])` is refused again with "the
  range is not one element".

`give` behaves the same: after a `take` in the accepted spelling,
`give(data[2 * index..2 * index + 2])` is refused with "the range is not one
element". A likely place: `check_element_at` in `src/kernel/iterated.rs`
compares the range against `index * stride` only, and the hint text is built
from the clause's `stride * k` shape.

```c filename=s.c
void f(int *data, int *occupied, int capacity, int index) { }
```

```click
resource pairs(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[2 * k..2 * k + 2];
        }
    }
}

verifying "s.c";

void f(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns pairs(data, occupied, capacity);
    requires 0 <= index; requires index < capacity; requires occupied[index] == 0;
} by {
    unfold(pairs(data, occupied, capacity));
    take(data[2 * index..2 * index + 2]);
    give(data[2 * index..2 * index + 2]);
    fold(pairs(data, occupied, capacity));
    execute();
    simp();
}
```

`click verify` prints:

```text
proof error:
  `take(data[(2 * index)..((2 * index) + 2)])` refused
  the range is not one element of the iterated ownership fact

tactic@17:
  take(data[2 * index..2 * index + 2]);
refused by: `take` (simple: a refusal within its documented behavior is a bug)
see: click docs take
```

Replacing both ranges with `index + index..index + index + 2` prints:

```text
proof error:
  `take(data[(index + index)..(index + index + 2)])` refused
  write the element as `base[2 * index + 0..]`, the clause's own shape
```

and replacing them with `2 * index + 0..2 * index + 2`, as that hint says,
prints the "not one element" refusal again. Replacing them with
`index * 2..index * 2 + 2` verifies.

## Acceptance criteria

- No `take` or `give` hint names a spelling that the same tactic refuses for
  the same element. For the `index + index` variant, the hint names a
  spelling that verifies when substituted (today `index * 2..index * 2 + 2`).
- The reproduction's refusal, if the clause-order spelling stays outside the
  documented form, says the spelling is the issue and names the accepted
  index-first spelling instead of "not one element". Accepting the
  clause-order spelling instead also satisfies this, with the reference
  updated to match.
- `take` and `give` agree on which spellings they accept and on the message.
- A regression keeps the source pattern: a `2 * k` stride clause with the
  element written `2 * index` in `take` and `give`, and the `index + index`
  hint case.
