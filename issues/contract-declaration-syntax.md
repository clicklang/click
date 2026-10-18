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
way, and so do C and C++ sidecars.

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
`examples/rbtree/rbtree-augmented/rbtree_size_copy.click`). In declaration order,
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
  declaration, `long` apart from `long long`. A head may write the source's
  scalar, struct, pointer, function-pointer and array typedef names
  (`json_bool`, `pid_t`, `node_t`, `node_ptr`, `unary f`, `triple values`).
- **C++.** Verified functions are written as C++ declares them:
  `Restore::Restore(int* slot)`, `Restore::~Restore()`,
  `void FeeFrac::operator+=(const FeeFrac& other)`, `bool FeeFrac::IsEmpty() const`,
  `static int64 FeeFrac::Div(...)`, `choose<true>(...)`, with `this` implicit
  and records named without `struct`. A member of a class template instance
  is written with the instance, `Stored<long long>::Read`, and a head's types
  write records by their C++ paths, `std::span<int>&`; diagnostics, claim
  labels and proof steps name functions the same way. An `extern` head for a
  system-header function is its C++ declaration too,
  `extern int ministd::Box::get() const`. A `contract` head is a free function
  type in C++ types, `contract int PositiveRead(const State& state)`. A
  function-pointer parameter to a `noexcept` function is a callback, as in C:
  `requires Doubling(f)` gives a call through it a contract, and a caller
  passing `&twice` shows `Doubling(&twice)`. A function-pointer local holds
  `&f` or another pointer, and a pointer can be passed on; reassignment and
  pointers in memory are refused. A lambda that captures nothing can be
  passed for a function pointer, named `caller::(lambda#0)`, and a
  `std::function` parameter holds a lambda capturing scalars by copy, a
  function, or another `std::function`; its contract implies it is not
  empty. Diagnostics and proof steps (`executes`,
  `step(callee(...))`) still name functions by the importer's names.
- **Rust.** Verified functions in native form, including `impl Drop for Guard`
  and module paths. A named contract is `contract fn Doubling(x: i32) -> i32`,
  and a `fn(i32) -> i32` parameter is a callback under it, with a crate
  function item passed for one. `extern fn` states the trusted contract of
  a scalar `safe fn` in an `unsafe extern "C"` block, the head naming its
  parameters. A closure that captures nothing can be passed for a `fn`
  pointer; the sidecar names it as rustc does,
  `fn closures::caller::{closure#0}(y: i32) -> i32`. A closure capturing
  scalars can be passed for a `&dyn Fn` or `impl Fn` parameter, its
  contract naming its captures, and a function item for an `impl Fn`. No
  functions of other crates. A
  diagnostic's suggested refinement theorem still uses the importer's name
  and C's `&f` spelling.

## Work, in delivery order

1. **Unify C.** Done: handle clauses in `contract` bodies are its proof
   parameters, `step(Name, { handle: value })` binds them, the retired forms
   are refused and migrated, and a head must have exactly its declaration's
   C types. Done: a head writes a verified source's scalar, struct,
   pointer, function-pointer and array typedef names, `u32`, `json_bool`,
   `node_t`, `node_ptr`, `unary f`, `triple values`.
2. **Native C++ heads.** Done for verified functions: qualified members with
   implicit `this`, constructors, destructors, `operator` names, `const` and
   `static` members, and `bool` function template arguments, with the corpus
   migrated. Done: class template arguments in heads
   (`Stored<long long>::Read`), as Clang prints the instance, and C++ names
   in diagnostics, claim labels and proof references to functions
   (`step(FeeFrac::IsEmpty(...))`, `&FeeFrac::EvaluateFeeDown`, `executes`
   targets). As the Rust importer does, the C++ importer names each
   function by an injective encoding of its path, which every diagnostic
   decodes. Done: a head's types write records by their C++ paths,
   `std::span<int>&` and `Box<int, false>&`, the instance printed without
   defaulted arguments. Remaining: diagnostics print a record type by its
   layout name.
3. **`extern` and `contract` for C++ and Rust.** Done: native C++ `extern`
   heads, members included, and calls through C++ function-pointer
   parameters under a named contract, and Rust `contract fn` with calls
   through `fn` pointers, Rust `extern fn` for `extern` block items, and
   C++ function-pointer locals and forwarded pointers, and Rust closures
   that capture nothing passed for a `fn` pointer, named
   `caller::{closure#0}`, and capturing closures and function items
   passed for `&dyn Fn` and `impl Fn` parameters, and C++ lambdas that
   capture nothing passed for a function pointer, named
   `caller::(lambda#0)`, and `std::function` parameters holding lambdas
   that capture by copy, functions, or other `std::function`s, whose
   contract implies they are not empty. Decided 2026-10-14: a capturing closure's contract
   names its captures as the body does (`ensures result == y + k;`), and a
   callee states what it needs of the closure with a parameterized named
   contract, whose value parameters are body clauses `let amount: i32;`
   attached as `Adds(f, { amount: k })`. Parameterized contracts are done
   for C and Rust function pointers, through automatic formation at
   `&f`, and for capturing closures by contract-to-contract refinement, and
   refinement and execution theorems conclude them with the values fixed.
   C++ and Rust function values reach them through the C++ exporter and
   Charon, with the same refinement check as C (`Comparator(&f)`).
4. **Base-class and trait method interfaces.** A contract on a C++ virtual
   method or a Rust trait method is the interface for that method. Each
   override or `impl` is checked against it with the named-contract
   refinement judgment. Dynamic dispatch through a base pointer or
   `dyn Trait` uses the interface. Standalone `contract` declarations remain
   for function values. Done for Rust: a sidecar `trait crate::Shape { fn
   area(&self, ...) { ... } }` states the interface, calls through a trait
   bound or `&dyn Shape` are checked against it, and each `impl` method,
   named `<crate::Square as crate::Shape>::area`, inherits it: decided
   2026-10-15, the interface's `ensures` join the implementation's own and
   its proof establishes them, and its `requires` apply when the
   implementation writes none; written `requires` must follow from the
   interface's. Object state is done for `&self` and `&mut self`, shared
   and mutable object references: a trait's `function size(self) -> i32;` is a field of its
   sealed object resource, each `impl` defines it from its fields and is
   verified on its own memory against an `_iface` contract, and the
   importer packs the struct into the object at generic instantiation and
   `dyn` coercion; a shared reference keeps the struct's memory lent for
   the call, so its caller keeps every field; a mutable reference may
   change the state, which its `ensures` read as new and `old(...)` as at
   entry. Done: an implementation, or a C++ override, that names the
   interface's parameters otherwise reads its clauses with its own names.
   Done for generic traits: `trait p::Scale<T>` states every instance's
   interface and `trait p::Scale<i32>` adds an instance's clauses;
   implementations at scalar instances refine them, and the generic
   block's `function`s, `items(self) -> List<T>`, are each instance's
   object fields at its types. Done: a generic block is checked once
   for every type, its type parameters abstract types whose values have
   `==` and `!=` only. Done: generic implementations, `impl<T> Keep<T>
   for Echo`, and generic functions over a type parameter's values are
   verified once for every type, and a call at scalar types uses the
   generic contract at those types. Done: a type parameter's values in
   memory, as a generic struct's fields, `struct Cell<T>`, for generic
   free functions over the struct and its own methods, `impl<T> Cell<T>`,
   verified once with each instance's contract read at its own layout.
   Remaining: a generic block whose object carries state is read at each
   instance only; a reference to a value of `T`; and a generic call from
   generic code. Done for default methods: the `trait`
   block writes a default method's interface with the proof of its default
   body, verified once with calls of the trait's methods under their
   interfaces; an `impl` that overrides it refines it. Done for C++
   virtual methods without object state: a virtual method's contract is the
   interface a call through it assumes, each override in the source
   inherits it and is checked to refine it, a pure virtual method's contract
   is written `extern`, and polymorphic classes with one polymorphic base
   are admitted by reference. Object state is done for `const` and mutable
   methods and references: a `class Shape { function size(this) -> int32; }`
   block declares it, each direct subclass defines it on its own memory and
   is verified there against an `_iface` contract, and the importer packs
   the subclass into the object where a reference converts to the base.
   A mutable receiver or reference may change the state, which its
   `ensures` read as new and `old(...)` as at entry. A polymorphic local is
   built by its explicit constructor when the constructor reads no `this`
   and its base has no fields; the compiler's vtable setup is trusted. A
   defaulted, implicit or empty virtual destructor, of any access, only
   resets the vtable pointer and runs no proof code; a class's own
   destructor with a body is verified as any destructor is, over a base
   whose destruction runs none. A defining class's `const` method views its
   memory, so its callers keep every field. A `const Shape&` conversion
   keeps the object's memory lent until the call returns, so its caller
   keeps every field too. A base with fields is built by its own
   constructor, named first in the derived constructor's initializer list.
   A base destructor with effects runs after the derived class's written
   destructor, on the base subobject. A class may derive from a defining
   class, redefining its functions or inheriting them through its base
   part, and override its methods, each keeping the object class's
   interface read with its own definitions; a reference to a class another
   derives from then holds the object, and a call through it is checked
   against that interface. A class may inherit a defining class's method
   where the functions its interface reads are defined alike.

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
