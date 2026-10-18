# Nightly two-parent authority fixture rejects its original proof

Soundness: incomplete. The existing nightly regression rejects its unchanged
positive fixture before checking any named-output expansion or negative
control. This does not demonstrate acceptance of a false claim; the cause
may be contract drift rather than a verifier defect.

Reproduced on master ec61898d0142e72332e973bf3b0e3ca0d4fa3ed4 with Rust
1.98.1 and the ordinary unoptimized test profile:

```sh
RUST_MIN_STACK=8388608 cargo test --lib \
  surface::tests::authority_conditional_release_tests::authority_nonterminal_detach_keeps_folded_named_output_once \
  -- --exact --include-ignored --nocapture
```

The unchanged test reads mdtests/shared_heap_two_parent_caller.md and fails
at its first `verify_c0_project`, before rewriting any tactic. The diagnostic
identifies caller.contract, tactic 0, at this existing C statement:

```c
parent_attach(first, kid);
```

```text
call to `parent_attach` parameter `kid` requires original object class
`struct child` or null
```

The printed context includes `kid != 0`, `views *kid`, `owns
child_control(kid)`, and `owns child_ref(kid)`. The child_control resource
contains allocation(kid, 8), the child object, and authority(child_ref(kid)).
The fixture's existing C parameter is `struct child* kid`.

The same rejection occurs on 9da88f12684c4d721e3cdeadc806d1df1b4bf318,
so this is not caused by the later input-naming change or test optimizations.

Acceptance: establish whether this supported contract needs an origin promise
or the verifier loses available object-class evidence; fix the appropriate
boundary while retaining the native C and the original complete-project
positive check. The nightly test must then reach and pass every selected
parent_detach expansion and still reject its duplicated-survivor control.
Do not scope away the failing caller merely to make this test pass.
