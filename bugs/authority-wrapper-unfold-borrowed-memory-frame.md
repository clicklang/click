# Authority wrapper unfolding fails beside borrowed memory

A post-return `unfold` of an ordinary authority wrapper should preserve unrelated
borrowed memory and certify the returned child resource. The supported wrapper
case in `authority_transfer_wrapper_preserves_each_existing_child` passes, but
adding ownership clauses for two unrelated struct fields makes return
certification reject the same unfolding proof.

Reproduced on the parent of `d441cd840588a4106fd83f7df61a11db8e9d696f`
(`e2fddbb7b`), as well as with the selected-memory normalization repair. It is
independent of projected C++ calls. Folding the wrapper with this same memory
frame succeeds and has a passing regression in
`authority_transfer_wrapper_preserves_adjacent_mixed_width_memory_frame`.

Use `verify_c0_project` with `ResourceSemanticsMode::Authority`, the following
`wrapper.click`, and the C source below (the existing wrapper test module's
`project` helper supplies the profile):

```click
 authorized abstract resource member(object: int32);
 authorized resource held(object: int32) { contains member(object); }
 verifying "wrapper.c";
 int32 package(int32 object, struct Frame* frame) {
     consumes member(object);
     owns member(object);
     owns frame->wide;
     owns frame->narrow;
     produces held(object) by {
         execute();
         fold(held(object));
     }
 }
 int32 unpack(int32 object, struct Frame* frame) {
     consumes held(object);
     owns frame->wide;
     owns frame->narrow;
     produces member(object) by {
         execute();
         unfold(held(object));
     }
 }
```

```c
struct Frame { int64 wide; int32 narrow; };
int32 package(int32 object, struct Frame* frame) { return object; }
int32 unpack(int32 object, struct Frame* frame) { return object; }
```

Observed in approximately 0.25 seconds:

```text
could not certify contract for `unpack`: exact symbolic execution did not
establish every contract claim; execution path 0 is invalid: the certified
path is not safe: RuntimeError(FunctionContract("function body does not yet
establish its joint returned resource units"))
```

The diagnostic identifies `unpack.ensures_2`, tactic `[1]`. Investigate the
checked return-resource transition and post-return wrapper rewrite replay;
do not loosen resource exchange checks or normalize away borrowed-clause
boundaries.

Acceptance criteria:

- The unchanged reproduction verifies, expands, and rechecks retained proof.
- The regression preserves both fields and rejects missing child authority,
  duplicate returned ownership, and removal of an unrelated memory unit.
- Deterministic work stays bounded as unrelated holdings increase.
- The existing authority-wrapper and Markdown proof corpus passes, including
  `population_mutex_hidden_unit_at_release`'s checked nested-goal rejection.
