# A loop loses an owned map it reaches through a struct field

Soundness: incomplete. Click refuses a loop preservation step that the
loop's own frame covers. No false acceptance is known.

Priority: P2.

Both fixtures write an array that the function owns through a pointer field
of a struct it views: `arena->occupied[i]`, and `arena->data[i]` reached
through `region->arena`. Inside `preserve`, the first `step()` of the body
refuses the store, reporting that the pointer arithmetic left the
pointed-to object. That holds even though the loop's frame owns the array
and the context holds `0 <= i < capacity`. On master `071ed68b` the first
fixture instead failed with a missing `owns` fact for the stored cell; the
held `owns` covered it only under bounds the step did not prove. Both
symptoms show the store not tied to the loop head's field value: the map's
range is written through `*(the pointer value at this program point)` or
`old(...)`. The two fixtures now fail the same way, so they share a file
until a reduction shows otherwise.

On master `071ed68b`, `click verify` gives byte-identical output with and
without the sequential-loop clause indexing (branch `seqloop3`). The fixture
still fails after rebasing onto master `ee00067b`. It is in `NIGHTLY` in
`tests/mdtests.rs`, so the gate does not run it.

```sh
MDTEST_FILTER=loop_entry_keeps_unfolded_state_fields_beside_its_owned_map RUST_MIN_STACK=8388608 \
  cargo nextest run --test mdtests
```

```text
expected pass, but failed: `mark_all.contract` tactic 3 (`loop`), `preserve` tactic 0: `step()` produced undefined behavior: pointer arithmetic left the pointed-to object
error kind: proof error
tactic: step
operation: `arena->occupied + i`
C statement at loop_entry_keeps_unfolded_state_fields_beside_its_owned_map.c:10:9: `arena->occupied[i] = 1;`
proof context:
pure facts: [<unnamed A> < old(arena->capacity), 0 <= <unnamed A>, 0 <= old(arena->capacity), <unnamed A> <= old(arena->capacity), old(arena->capacity) <= 1073741823, (uint32)old(arena->capacity) <= 1 …
resource facts: [owns arena->occupied[0..arena->capacity], views *arena, owns i[0..4]]
stage: proof step
location: tactic 5
recent premises (showing 8 of 20):
0 <= i and i <= old(arena[2])
```

```sh
MDTEST_FILTER=loop_frame_keeps_a_two_hop_map_beside_a_written_array RUST_MIN_STACK=8388608 \
  cargo nextest run --test mdtests
```

```text
expected pass, but failed: `clear_data.contract` tactic 4 (`loop`), `preserve` tactic 1: `step()` produced undefined behavior: pointer arithmetic left the pointed-to object
error kind: proof error
tactic: step
operation: `arena->data + i`
C statement at loop_frame_keeps_a_two_hop_map_beside_a_written_array.c:17:9: `arena->data[i] = 0;`
proof context:
pure facts: [<unnamed A> < old(*<pointer A>), 0 <= <unnamed A>, 0 <= old(*<pointer A>), <unnamed A> <= old(*<pointer A>), old(*<pointer A>) <= 1073741823, (uint32)old(*<pointer A>) <= 1073741823u32, ( …
resource facts: [owns ((char *)region)[((*region->arena - …) * 4)..(((*region->arena - …) + *(the pointer value at this program point)) * 4)], views *region, views ((char *)region->arena)[0..24], view …
stage: proof step
location: tactic 7
recent premises (showing 8 of 23):
forall (k: int32) { 0 <= k and k < old(arena[4]) implies at(<state A>, *<pointer A>) == old(*<pointer A>) }
```

Invariant: a loop whose frame owns `p->f[0..n]` can store to `p->f[i]` in its body under `0 <= i < n`, whether `p` is a parameter or is reached through another struct.

Acceptance: both fixtures pass unchanged and leave `NIGHTLY` if they are fast enough. A reduced regression in the gate keeps the field-reached map pattern.
