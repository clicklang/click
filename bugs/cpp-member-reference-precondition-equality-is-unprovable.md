# A C++ member-reference precondition equality is unprovable

Soundness: incomplete. A caller that binds a callee's reference parameter to
`pair.first` cannot establish the callee's precondition
`&r == &pair.first`, a true equality of one member address with itself. The
call is refused; no false acceptance is involved. It verified on master
`3573f404f`, before the subobject-extent Phase C work
(`design/pointer-subobject-extents.md`) and the contract pointer-equality
designation rule (D2), and is refused on master `8d8a621cc`.

## Reproduction

```cpp filename=refp.cpp function=caller profile=normal_only
struct Pair { int first; int second; };
int reach(Pair& pair, int& r) noexcept { return *(&r + 0); }
int caller(Pair& pair) noexcept { return reach(pair, pair.first); }
```

```click
verifying "refp.cpp";
int32 reach(struct Pair& pair, int32& r) {
    views pair.first;
    views pair.second;
    requires &r == &pair.first;
    ensures result == pair.first;
} by { execute(); simp(); }
int32 caller(struct Pair& pair) {
    views pair.first;
    views pair.second;
    ensures result == pair.first;
} by { execute(); simp(); }
```

On `8d8a621cc` the caller's `execute()` stops at the precondition:

```text
precondition clause 3 of `reach`: condition-certificate premise search did
not derive `&pair == &pair` from 1 ambient condition facts:
[<unnamed A> == old(pair)]
```

Both sides print as `&pair`. The argument is the C++ member address
`pair.first`, and the contract's `&pair.first` is the same member, so their
addresses and subobjects agree. The obligation that remains is apparently the
equality of the two extents' starts, spelled differently: one through the
caller's reference binding, one through the contract's evaluation of `pair`.
The C analogue, with a pointer parameter `q` and `requires q == &p->first`,
verifies (`mdtests/a_member_pointer_parameter_fills_its_member_clause.md`).

## Acceptance

- The reproduction verifies, as it did on `3573f404f`; add it as an mdtest
  with `expect pass`.
- Its negative sibling stays refused:
  `mdtests/cpp_a_member_reference_parameter_keeps_its_subobject.md` reads
  `*(&r + 1)` and must keep failing with `access outside the subobject the
  pointer designates`.
- Equality of two spellings of one member's start is decided by the graph,
  not by premise search.
