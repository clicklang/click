# One contract declaration syntax, native in C, C++ and Rust

Priority: P2.

Soundness: not soundness. This is surface syntax and frontend coverage. One
precision gain is noted under native type names: a C head written with Click's
`int64` matches both `long` and `long long`, which C keeps distinct. No false
acceptance from that looseness is known, because both have the same
representation under the supported LP64 ABI.

P2: no launch claim depends on the spelling. The rbtree augmentation callbacks
use named contracts, though, so landing step 1 before launch would let the
launch demo show the final syntax.

## Accepted design, 2026-10-14

The user and an agent agreed on these decisions. Migration cost is not a
constraint: optimize for the long-term language, and migrate the whole corpus
(examples, mdtests, fixtures, integrations, docs) to it.

### The rule

A contract is a target-language function declaration followed by a clause
block. A prefix says what the declaration names:

| Prefix | Names | Proof |
| --- | --- | --- |
| none | a function in the verified sources | `by ...`, default `auto` |
| `extern` | a function outside the verified sources, trusted | none allowed |
| `contract` | an interface: a named function type, not a function | none allowed |

The head is written the way the target language writes the declaration. In C
it uses C declaration syntax, in C++ C++ declaration syntax (qualified member
names, implicit `this`, references, `const` methods), and in Rust Rust item
syntax (`fn`, `impl` blocks, module paths). Rust sidecars already work this
way. C sidecars mostly do; C++ sidecars do not yet.

```click
// C
int clamp(int x, int lo, int hi) { requires lo <= hi; ... } by auto;
extern int g(int x) { requires x >= 0; ensures result == x; }
contract int Comparator(int left, int right) { requires 0 <= right; ... }
contract int Read(int* p) {
    owns cell: marked_cell(p);
    ensures cell.revision == old(cell.revision);
}
```

```click
// C++
Restore::Restore(int* slot) { owns this->p; ... } by { execute(); simp(); }
Restore::~Restore() { ... }
FeeFrac& FeeFrac::operator+=(const FeeFrac& other) { ... }
extern int g(int& x) { ... }
contract int Comparator(int left, int right) { ... }
```

```click
// Rust
fn choose(x: i32) -> i32 { ... } by { execute(); simp(); }
impl Counter { fn get(&self) -> i32 { ... } }
extern fn g(x: i32) -> i32 { ... }
contract fn Comparator(left: i32, right: i32) -> i32 { ... }
```

### Proof-only parameters are body clauses

A named contract's resource handles are declared in its body, as concrete
functions already declare them (`owns source: size_metadata(rb_old);` in
`examples/rbtree-augmented/rbtree_size_copy.click`). In declaration order,
the named handles in a `contract` body are its proof parameters. This removes
the forward reference in today's
`contract Read(cell: marked_cell(p)) for int32(int32* p)`, where `cell` names
`p` before `p` is declared.

### One application syntax

| Use | Spelling |
| --- | --- |
| Attach an interface to a function value (a proposition) | `Comparator(callback)`, `Comparator(&compare)` |
| Select a contract with no handles at a call | `step(Comparator)` |
| Select a contract with handles | `step(Read { cell: first })` |
| Bind the handles of a formed fact | `Read(&read) as { cell: c }`, as today |
| Open an interface in a refinement proof | `unfold(Comparator)`, as today |

The record form binds handles by name. It reuses the syntax of `as { ... }`
and `fold`, and it does not collide with the proposition form, which takes a
function value in parentheses. `step(Identity())` and the positional
`step(Read(first))` are retired.

### Native type names in heads; Click type names in specifications

Positions that restate a declaration (the head of a verified, `extern`, or
`contract` declaration) use the target language's types, exactly as the source
spells them: `int`, `size_t`, `unsigned long`, typedef names such as
`json_bool`, `const char*`, `int&`, `&mut [u8]`. Click checks the head against
the real declaration, including the distinctions C keeps: `long` is not
`long long`, and `int64_t` is `long` in user space but `long long` on the
kernel target. A mismatch is reported against the source declaration.

Specification positions keep Click's names, the same in every target
language: `forall (i: int32)`, `function f(x: int32)`, `theorem` parameters,
resource `field value: uint64;`, `Integer`. The specification language is
shared, so a library theorem or model means the same in a C, C++ or Rust
sidecar.

Sidecars already accept C's standard spellings (`docs/reference/language/c.md`,
"Supported types"), so for C this is a convention plus the exact head check,
not a new type mapping. Today's example sidecars write `int32` in heads about
700 times and `int` 16 times.

## Current state

- **C.** Verified functions, `extern`, and two coexisting named forms: an older
  one, `contract int32 Comparator(int32 left, int32 right) { ... }`, in about
  240 files, and a newer one,
  `contract Read(cell: marked_cell(p)) for int32(int32* p) { ... }`, in about
  35. They select differently: `step(Identity)` against `step(Identity())`.
- **C++.** Verified functions only, written in a C-shaped, mangled form:
  `void Restore_constructor(struct Restore* this, int32* slot)`,
  `void FeeFrac_operator_add_assign(struct FeeFrac* this, const struct FeeFrac& other)`.
  No `extern` or named contracts.
- **Rust.** Verified functions in native form, including `impl Drop for Guard`
  and module paths. No `extern` or named contracts.

## Work, in delivery order

1. **Unify C.** Parse handle clauses in `contract` bodies as proof parameters.
   Add `step(Name { handle: value })`. Retire the `(...) for` form, the
   positional and empty-parenthesis applications, and Click type names in
   heads. Add the exact head-against-source type check. Migrate the corpus
   and docs.
2. **Native C++ heads.** Qualified member functions with implicit `this`,
   constructors and destructors by their C++ names, operators by `operator`
   names, `const` methods, and template instances spelled as C++ spells them.
   Migrate the C++ fixtures, `examples/basic-cpp`, and
   `integrations/bitcoin-core-money-range`.
3. **`extern` and `contract` for C++ and Rust.** Function pointers in both,
   `std::function` in C++, and closures (`impl Fn`, `&dyn Fn`) in Rust,
   through the C++ exporter and Charon, with the same refinement check as C
   (`Comparator(&f)`).
4. **Base-class and trait method interfaces.** A contract on a C++ virtual
   method or a Rust trait method is the interface for that method. Each
   override or `impl` is checked against it with the named-contract
   refinement judgment. Dynamic dispatch through a base pointer or
   `dyn Trait` uses the interface. Standalone `contract` declarations remain
   for function values.

## Intended regressions

Each step adds checked mdtests or fixtures, and retains the original source
patterns:

- C: one file each for a verified function, an `extern`, a handle-free
  `contract`, and a `contract` with a handle selected by
  `step(Read { cell: first })`; a `long` head against a `long long`
  declaration, refused with the source declaration named; an old-form
  application, refused with the replacement named.
- C++: a constructor, a destructor, `operator+=`, and a `const` method
  written natively; an `extern`; a `contract` on a function pointer and on a
  `std::function`; a virtual method interface with one conforming override
  and one refused override.
- Rust: an `extern fn`; a `contract fn` on a function pointer and a closure;
  a trait method interface with one conforming `impl` and one refused `impl`.

## Acceptance criteria

- One grammar rule covers all three kinds of contract in every target
  language: a native declaration, an optional `extern` or `contract` prefix,
  a clause block, and an optional proof for verified functions only.
- No sidecar, fixture, or reference page uses the retired forms, and the
  parser refuses each retired form with its replacement.
- Every head is checked against its source declaration's exact types.
- `docs/reference/language/` documents the rule once, with one example per
  target language, and `docs/reference/coverage.md` reports `extern`,
  `contract`, and method interfaces for C++ and Rust.
