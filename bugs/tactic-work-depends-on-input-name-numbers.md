# Tactic work depends on the numbers of a function's input names

Soundness: not soundness. Renumbering changes how much work a proof takes,
and whether it fits its budget. No observed renumbering made a false claim
verify.

A function's pointer inputs are named `Variable(100_000 + n)`, numbered in
whole-file verification order (`input_pointer_variable` in
`src/surface/lowering/resource_lowering.rs`). The numbers carry no meaning,
but a tactic's deterministic work depends on them. Load-variable ids are hash
slots of the load's snapshot and address (`mint_load_variable_identity` in
`src/kernel/eval/memory_loads.rs`). Snapshots order by content hash first
(`impl Ord for SharedCMemory` in `src/kernel/primitives.rs`). Both change
when an input's number changes, and so does the order in which closers try
facts and recorded snapshots. Adding, removing or reordering an unrelated
function with pointer parameters earlier in a sidecar renumbers every later
function's inputs. A proof's work should depend on the proof and the facts
it uses, not on which names other functions took first.

## Reproduction

A sidecar with `N` unrelated earlier functions, then `combine`:

```sh
for n in 1 2 4 8; do
  mkdir -p /tmp/names-$n
  {
    echo 'struct arena { int32* occupied; int32 capacity; };'
    echo 'struct region { struct arena* arena; int32 start; int32 end; };'
    for i in $(seq 0 $((n - 1))); do
      echo "void mark_$i(struct region* r, int32* cells) { cells[0] = $i; }"
    done
    echo 'int32 combine(struct arena* arena, struct region* first, struct region* combined) {'
    echo '    combined->start = first->start; combined->end = first->end;'
    echo '    combined->arena = arena; return combined->end - combined->start; }'
  } > /tmp/names-$n/pipe.c
  {
    echo 'verifying "pipe.c";'
    for i in $(seq 0 $((n - 1))); do
      echo "void mark_$i(struct region* r, int32* cells) { owns cells[0..1]; ensures cells[0] == $i; } by { execute(); simp(); }"
    done
    cat <<'EOF'
int32 combine(struct arena* arena, struct region* first, struct region* combined) {
    owns first->arena; owns first->start; owns first->end;
    owns combined->arena; owns combined->start; owns combined->end;
    requires first->arena == arena;
    requires 0 <= first->start; requires first->start <= first->end; requires first->end <= 1000;
    ensures combined->arena == arena;
    ensures result == combined->end - combined->start;
} by {
    step(); step(); step();
    have combined->arena == arena by auto();
    have combined->start == first->start by auto();
    have combined->end == first->end by auto();
    execute();
    simp();
}
EOF
  } > /tmp/names-$n/pipe.click
  CLICK_TIMINGS=1 target/release/click verify /tmp/names-$n/pipe.click 2>&1 |
    grep 'tactic combine.contract 0 step'
done
```

On master at filing, `combine`'s first `step()` spent 1,876, 2,142, 1,522
and 1,515 units for `N` = 1, 2, 4 and 8. Its proof and facts are the same at
every size. An experimental build that placed each function's inputs in a
64-name block chosen by hashing the function's name kept every name fixed.
There, all eight of `combine`'s tactics spent the same work at every `N`, and
`step()` spent 997.

Renumbering can also take a tactic past its budget. Apply the edit from
`arena_pipeline`'s second `have forall (k: int32) { 0 <= k and k <
arena->capacity implies arena->occupied[k] == 0 }` in
`examples/arena/arena_cells.click`: its inner `have at(f4,
combined->arena->occupied[k]) == at(f4, arena->occupied[k])` is closed by
`auto()` instead of `simp() using { at(f4, combined->arena) == arena; }`.
Master names the inputs in whole-file order. Its control `have` (statement
35, source tactic 347) then spends about 178,000 units selected and 172,000
in the whole file. With the block-per-name build, it exhausts the 2,500,000
unit control budget in both modes. A trace of the same tactic at commit
124bd4bfb, where the two modes named inputs differently, shows the cause. For
the premise `at(f4, combined->arena) == arena`,
`synthesize_surface_at_recorded_snapshots` spells
`load_int32_pointer(combined) == arena` at statement 34's entry under one
numbering. Under the other numbering it finds nothing at statements 35, 34 and
33 and uses a statement 32 spelling that does not check. The atomic closure
then fails, and `auto` tries the remaining derivations through
`simp premise surface at recorded snapshots`.

The same build also turned `examples/marked-linked-list` into a syntax error,
"a struct pointer cast applies to a `void *` parameter of the function under
contract". Some code reads meaning from input-name numbers.

## Intended regression

A deterministic test that verifies one function beside 1, 2, 4 and 8
unrelated earlier functions with pointer parameters, and asserts that each
of its tactics spends the same work at every size. Add a counterpart with a
direct renumbering of the inputs: a test-only offset applied when inputs are
named.

## Acceptance criteria

- A function's tactics spend the same work whatever numbers its inputs
  receive. The cause is either removed (orders and ids no longer derive from
  the numbers) or the numbers depend only on the function.
- The edited `arena_pipeline` verifies whichever names its inputs receive.
- Changing input numbers changes no parse or validation verdict.
- `a_functions_tactic_work_does_not_grow_with_earlier_unrelated_functions`
  tightens from its 20% band to equality.
