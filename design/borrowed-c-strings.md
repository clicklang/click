# Borrowed C strings: contract length binders and call-site assembly

Status: proposal for maintainer review. Nothing here is implemented.

`click::cstr` declares the borrowed C string (landed with this proposal):

```click
resource cstr_at(p: const uint8*, len: uint64) {
    views p[0..len + 1u64];
    fact len < 18446744073709551615u64;
    fact forall (k: uint64) { 0u64 <= k and k < len implies p[k] != '\0' };
    fact p[len] == '\0';
    fact forall (k: uint64) { 0u64 <= k and k < len + 1u64 implies defined(p[k]) };
}
```

The goal is `strlen` and `label_copy` contracts that hold the string under
`views`, so the trusted `memcpy`/`memcmp` can read under `views` (M3) without
narrowing a claim. Two pieces are missing: a contract cannot name a length its
C signature does not carry (c), and a caller that holds only the bytes cannot
pass a `cstr_at` it never folded (d).

## (c) The length is an instance binder's argument

### What exists

Contracts already have binders for resource instances. `owns cell: R(args);`
declares a contract proof parameter (`ContractDefinition::proof_parameters`).
A call binds it from an explicit map, `step(f(x), { cell: c })`, or
automatically when exactly one binding is possible, and never chooses between
two (proof-language rulings). `cell.field` reads a field of the bound
instance and `old(cell.field)` its entry value. Resource arguments already
admit `_` in authority patterns. Contract-level `let x = e;` is an abbreviation,
and `let x: T where P;` is a per-clause existential that the callee chooses.
Neither one is a single value that the caller chooses for the whole contract,
and the reference refuses `let ... where` in memory segments "until Click has a
contract-wide witness environment".

### Proposal: extend instance binders instead of adding a parameter form

```click
extern uint64 strlen(const uint8* bytes) {
    views s: cstr_at(bytes, _);
    ensures result == s.len;
}
```

This needs three extensions, and each one generalizes an existing form:

1. A binder on a `views` clause, and on a fieldless resource. Today a binder
   requires `owns` and fields. A `views` binder names a borrowed instance,
   which the callee cannot change.
2. `_` in a binder's arguments. The bound instance fixes that argument; the
   clause does not.
3. `s.param` projects a resource parameter by name, just as `s.field`
   projects a field. A parameter that shares a name with a field is refused at
   the declaration.

**Meaning.** The callee is proved for every instance that matches
`cstr_at(bytes, _)`, that is, for every `len`, and the facts of the instance
are its premises. The caller supplies the instance:

- automatically, under the existing rule: exactly one held `cstr_at` agrees
  with every argument that is not `_`;
- explicitly, by naming its own instance: `views str: cstr_at(src, n);` and
  `{ s: str }`;
- or, new and needed only for (d), by naming a resource term,
  `{ s: cstr_at(src, n) }`, which binds the instance with those arguments.

**Later clauses.** A binder is bound before the clauses that follow it are
evaluated, so `s.len` may appear in `ensures` and in later memory segments:
`owns dst[0..s.len + 1u64];` and
`requires separate(memory(dst[0..32]), memory(src[0..s.len + 1u64]));`. This is
the contract-wide environment that the reference says `let ... where` lacks,
limited to values that a held instance determines. A clause may name only
earlier binders.

**`old(...)`.** A `views` instance cannot change during the call, so
`old(s.len)` is `s.len`. For an `owns s: cstr_at(p, _)` binder, `s.len` reads
the returned instance's argument and `old(s.len)` the entry instance's, the
same rule as for fields.

**Expansion.** Binding is part of the simple call rule: it is deterministic,
indexed by family and base, and involves no search, as today's automatic
binders do. A bare `step()` therefore stays valid expanded text.
`click expand` writes `{ s: name }` when the caller's instance has a name, and
writes the resource-term form when the call assembles the instance as in (d).

**Not an executable ghost.** Nothing is passed at run time. The C call, its
ABI and the C source are unchanged. `s.len` is a universally quantified
contract variable, and the call rule instantiates it with the matched
instance's argument value. The kernel needs no new concept: it already binds
instance identities at a call, and it binds the argument value the same way.

**Elsewhere.** Dafny ghost parameters are explicit arguments at every call.
They are erased at compile time and need ghost-ness rules because they live in
executable code. VeriFast's `requires [?f]string(s, ?cs); ensures result ==
length(cs);` binds pattern variables from the matched heap chunk. That is the
closest match: the binder with `_` is VeriFast's `?len`, but Click refuses an
ambiguous match instead of taking the first chunk, and it offers an explicit
map.

**Alternative A.** A contract quantifier,
`forall (len: uint64); views cstr_at(bytes, len); ensures result == len;`, reads
exactly like the stated goal. The caller would supply `{ len: n }`, or it
would be inferred when one held instance determines `len`. The cost is that
call maps gain a second namespace (values beside instances), and inference has
to decide which clause determines `len`. Under B the instance carries the value
and binding stays one rule. **Recommendation: B.** A remains open if bare
names are preferred.

## (d) Call-site assembly of a viewed composite

**Rule.** At a call whose callee requires `views R(a)`, all of `a` is known
once binders are resolved; under (c), from `{ s: R(a) }`. Assembly applies
when the caller holds no instance `R(a)`, folded, owned or viewed, and `R`
qualifies:

- it has no fields, resource parameters, `let` witnesses, guards or matched
  arms;
- it has no child resources (`owns Q(...)` or named children);
- its memory clauses are `views` only (`owns` clauses lent as views is a
  possible extension and an open question below), and its other clauses are
  pure `fact`s.

`cstr_at` qualifies.

**Steps.**

1. Instantiate `R`'s body at `a`, one level.
2. Lend each `views` segment from the caller's holdings through the existing
   plain-view loan, the one that serves a `views p[lo..hi]` requirement today:
   from owned, viewed, literal or static storage, including a covered
   subrange.
3. Check each fact in the caller's state at the call, as a precondition with
   the same obligation and the same failure. A proof may state it with `have`
   before the call.
4. The callee's entry receives `views R(a)` exactly as from a folded loan.
5. At return the plain loans return as they do today. No `R` instance
   persists in the caller.

**Soundness.** Assembly is the existing `fold(R(a))` before the call and
`unfold` after it, performed by the call rule. A fold of a views-only body
checks the same facts against the same views, and unfolding a viewed instance
recovers exactly the loans it took. The callee sees what a folded instance
would give it: read access to the instantiated segments and the facts. The
lent bytes are shared-borrowed for the whole call, so the caller cannot write
them, the callee can only read them, and every memory fact checked at the call
stays true until the loan returns. The loan accounting is the existing
plain-view lending, unchanged. Assembly is never tried while a matching
instance is held, so it cannot duplicate an instance or shadow one.

**Cost.** Assembly runs only on a miss for an exact instance. It processes the
fixed clause list of one body: for `cstr_at`, one symbolic range
`p[0..len + 1]`, lent as one range with no per-byte work, and four facts
discharged as requirements. Nothing depends on the string's length, on
unrelated resources, or on proof history, and with no children there is no
recursion. Selection uses the existing indexed resource lookup by family and
base.

**Diagnostics.** A failure names the requirement and the assembly step:

- "call to `strlen` needs `views cstr_at(src, n)`; the caller holds none, and
  assembling it needs `views src[0..n + 1u64]`, which the caller does not
  hold";
- the unclosed fact, as a refused fold reports it, "requires an exact body
  fact `src[n] == '\0'`";
- for a body that does not qualify: "`R` cannot be assembled at a call: its
  body has child resources; fold it before the call".

**Not proposed.** A persistent fold, which would change the caller's state
invisibly; recursive assembly through children, whose cost grows with the
structure; assembly for `owns` or `consumes` requirements.

## Migration plan

1. Implement (c): `views` and fieldless binders, `_`, `s.param`, the
   resource-term map entry. Add mdtests for each, including ambiguity
   refusal, an `owns` binder with `old(s.len)`, and a later segment that
   names `s.len`.
2. Implement (d), with positive, missing-view, failed-fact and
   non-qualifying-body mdtests, and a scaling regression that grows string
   length and unrelated held resources.
3. Change the `strlen` library contract to
   `views s: cstr_at(bytes, _); ensures result == s.len;`. It now needs read
   authority, not only `viewable`. This deliberately strengthens the
   precondition, as M3 does for `memcpy`/`memcmp`. 29 mdtest files mention
   `strlen`, and 26 of them use `cstr::readable`:
   - Declaration and binding tests (redeclarations, kernel-target refusals,
     `<string.h>` binding, about 8) keep their shape. Their callers change
     only where they verify a call.
   - The `cstr_dynamic_*` (8) and plain-, signed-char caller-requirement
     tests (about 8) state `views s: cstr_at(src, _)`, or
     `views src[0..n + 1u64]` with the facts, so that the call assembles.
     The tests whose subject was `cstr::readable` transport (epochs, offset
     copies, writes) keep a variant that holds the predicate and refuses
     the call. That shows `viewable` alone no longer suffices.
   - `stdlib_every_symbol.md` and
     `strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md`
     use `views cstr_at(text, 0u64)`.
4. In `examples/label-build-flags`, `label_measure` and `label_copy` take
   `views s: cstr_at(src, _)`. They state
   `ensures s.len < 32u64 implies result == s.len;` and
   `ensures 32u64 <= s.len implies result == 31u64;`, and `label_copy` adds
   `requires separate(memory(dst[0u64..32u64]), memory(src[0u64..s.len + 1u64]));`
   and `ensures bytes::equal(dst, 0u64, src, 0u64, result);`. The
   obtain-and-transport proof becomes `execute()` plus arithmetic.
5. In `src/surface/tests/expansion_tests.rs`, the `read_terminator` fixture
   tests the source identity of a reordered `cstr::readable` requirement.
   It becomes an assembly fixture: `views haystack[0..known_len + 1u64]`,
   the facts, and `{ s: cstr_at(haystack, known_len) }` in the expanded
   proof. It still asserts that no hidden planning transitions occur.
6. In `src/surface/proof/surface_synthesis/tests.rs`, the strlen-shaped tests
   synthesize the guarded quantified `loadable` carrier that `cstr::readable`
   produced. If `memcmp`'s guarded `defined` range still produces that
   carrier after M3, they are renamed to C-string shapes. Otherwise they are
   retired with the shape.
7. Then M3: `memcpy`/`memcmp` read under `views`.

## Open questions for the maintainer

- B (instance binder, `s.len`) or A (`forall (len: uint64);`, bare `len`)?
- The resource-term map entry `{ s: cstr_at(src, n) }`: accept it, or require
  the caller to name a held instance and rely on assembly only when the
  arguments follow from the callee's clause?
- Should assembly also lend a body's `owns` clauses as views?
- Should `strlen` keep its `cstr::readable`-based guarantees beside the new
  ones during the migration, or switch in one step?
