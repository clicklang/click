# Shared-heap returns are refused for a different published state

Five nightly mdtests fail on master `256fa769b` with the same refusal:

```sh
MDTEST_FILTER=shared_heap CLICK_NIGHTLY=1 cargo test --release --test mdtests
```

```text
`parent_read_payload.contract` proof step tactic 6: return observation has a
different published state
```

- `shared_heap_population_certification`
- `shared_heap_population_lifecycles`
- `shared_heap_two_parent_caller`
- `shared_heap_two_parent_branch_release`: expects a refusal for
  `count(child_ref(kid)) == 2` and gets this one first
- `iterated_ownership_allocate_one`: `claim.contract` proof step tactic 4

All five are listed in `NIGHTLY` in `tests/mdtests.rs`, so the gate does not
run them. They passed in this session's nightly run on master `fefd3ac92`.
`12cf1a803` ("Certify call-produced resource unfolds after return") is a
likely cause, since each failing step returns after a call that produced a
resource, but the breaking commit is not bisected.

The broken invariant: a `return` whose published state matches its
observation is accepted. Here the proofs and their C are unchanged, and the
refusal names no differing resource or fact, so it is either a false
refusal or a refusal without an actionable diagnostic.

Acceptance:
- The five mdtests pass again, or `shared_heap_two_parent_branch_release`
  reports its intended refusal, with no change to their C.
- When the published state does differ, the refusal names the first
  resource or fact that differs.
- A gate mdtest covers a call that produces a resource, unfolds it after
  return, and returns, so the next regression is caught by the gate.
