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
| Select a contract with handles | `step(Read, { cell: first })` |
| Bind the handles of a formed fact | `Read(&read) as { cell: c }`, as today |
| Open an interface in a refinement proof | `unfold(Comparator)`, as today |

The map binds handles by name. It is the map a call step already writes,
`step(callee(args), { binder: instance })`, after the contract's name, and it
does not collide with the proposition form, which takes a function value in
parentheses. `step(Identity())` and the positional `step(Read(first))` are
retired.

### Native type names in heads; Click type names in specifications

Positions that restate a declaration (the head of a verified, `extern`, or
`contract` declaration) use the target language's types, as the source writes
them: `int`, `size_t`, `unsigned long`, typedef names such as `json_bool`,
`const char*`, `int&`, `&mut [u8]`. Click checks that the head has exactly
the declaration's types, including the distinctions C keeps: `long` is not
`long long`, and `int64_t` is `long` in user space but `long long` on the
kernel target. A mismatch is reported against the source declaration.

Decided 2026-10-14: the check is exact type identity, not spelling. Writing
the head the way the source spells it is a style convention
(`docs/style.md`); enforcing spelling would need the C frontend to keep each
declaration's text through typedefs and macros, and catches no type error
that exact identity misses.

Specification positions keep Click's names, the same in every target
language: `forall (i: int32)`, `function f(x: int32)`, `theorem` parameters,
resource `field value: uint64;`, `Integer`. The specification language is
shared, so a library theorem or model means the same in a C, C++ or Rust
sidecar.

Sidecars already accept C's standard spellings (`docs/reference/language/c.md`,
"Supported types"), and Click's C dialect accepts `int32`, `uint64` and the
other Click names as C type names, which most corpus C sources use. A head
that writes `int32` for such a source already writes the source's spelling.

## Current state

- **C.** Verified functions, `extern`, and one named form,
  `contract int32 Read(int32* p) { owns cell: marked_cell(p); ... }`, whose
  handles are its named `owns` and `consumes` clauses, selected by
  `step(Read)` or `step(Read, { cell: first })`. The parameter-list form and
  the `step(Name())` and `step(Name(instance))` applications are refused with
  their replacements. A head must have exactly the C types of its
  declaration, `long` apart from `long long`. Typedef names other than the
  standard ones (`json_bool`, `pid_t`) are not yet accepted in heads.
- **C++.** Verified functions are written as C++ declares them:
  `Restore::Restore(int* slot)`, `Restore::~Restore()`,
  `void FeeFrac::operator+=(const FeeFrac& other)`, `bool FeeFrac::IsEmpty() const`,
  `static int64 FeeFrac::Div(...)`, `choose<true>(...)`, with `this` implicit
  and records named without `struct`. A member of a class template instance
  (`Stored<long long>`) keeps the mangled name and explicit receiver, since a
  head does not yet spell class template arguments. An `extern` head for a
  system-header function is its C++ declaration too,
  `extern int ministd::Box::get() const`. A `contract` head is a free function
  type in C++ types, `contract int PositiveRead(const State& state)`. A
  function-pointer parameter to a `noexcept` function is a callback, as in C:
  `requires Doubling(f)` gives a call through it a contract, and a caller
  passing `&twice` shows `Doubling(&twice)`. A pointer is only called, not
  stored or forwarded, and `std::function` is not imported. Diagnostics and proof steps (`executes`,
  `step(callee(...))`) still name functions by the importer's names.
- **Rust.** Verified functions in native form, including `impl Drop for Guard`
  and module paths. A named contract is `contract fn Doubling(x: i32) -> i32`,
  and a `fn(i32) -> i32` parameter is a callback under it, with a crate
  function item passed for one. No `extern`, closures or `dyn Fn`. A
  diagnostic's suggested refinement theorem still uses the importer's name
  and C's `&f` spelling.

## Work, in delivery order

1. **Unify C.** Done: handle clauses in `contract` bodies are its proof
   parameters, `step(Name, { handle: value })` binds them, the retired forms
   are refused and migrated, and a head must have exactly its declaration's
   C types. Remaining: accept a source's own typedef names in heads.
2. **Native C++ heads.** Done for verified functions: qualified members with
   implicit `this`, constructors, destructors, `operator` names, `const` and
   `static` members, and `bool` function template arguments, with the corpus
   migrated. Remaining: class template arguments in heads (`Stored<long long>`,
   `std::span<int>`), and C++ names in diagnostics and in proof references to
   functions.
3. **`extern` and `contract` for C++ and Rust.** Done: native C++ `extern`
   heads, members included, and calls through C++ function-pointer
   parameters under a named contract, and Rust `contract fn` with calls
   through `fn` pointers. Remaining: storing and forwarding C++ function
   pointers, `std::function` in C++ (whose call operator throws when
   empty), Rust `extern fn`, and closures (`impl Fn`, `&dyn Fn`) in Rust,
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
  `step(Read, { cell: first })`; a `long` head against a `long long`
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
