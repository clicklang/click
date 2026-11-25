# Typed Surface

Status: proposed 2026-11-25; direction agreed with the maintainer.

## Pipeline

Click turns proof text into kernel terms in three steps, each producing its
own Rust type:

| Step | From | To | Does |
|---|---|---|---|
| parse | text | **Syntax** | builds the tree as written; nothing is inferred |
| elaborate | Syntax | **Surface** | resolves names, infers every type and kind, fills in what the text leaves implicit, and checks; an ill-typed proof is one that fails to elaborate |
| lower | Surface | **Kernel** | resolves Surface names to kernel identities and builds the efficient form; infers nothing |

Going back:

| Step | From | To | Does |
|---|---|---|---|
| raise | Kernel | Surface | transcribes every kernel distinction and adds spellings from retained names and provenance |
| print | Surface | text | may leave out what elaboration would infer back, such as a cast or a `to_integer`; when unsure it prints the explicit form |

## The rule: inference reads context, lowering is compositional

Type inference depends on syntactic context. What `1` or `a - 1` means
depends on what surrounds it: the other operand of a comparison, the parameter
it is passed to, the declarations in the file. It cannot be decided one node at
a time, so it happens in elaboration, which sees the whole file.

Lowering is compositional. A node's kernel term is built from the node itself,
its children's kernel terms, and the program state it is lowered at, and from
nothing else: not its parent, not its siblings, not which function reached it.
The program state is resolution, not inference: `p->x` lowers to the read at
the address and memory version that state gives it, the same answer for the
same node at the same point.

This gives a test for the code. Lowering code that looks at a node's parent or
siblings, or behaves differently depending on its caller, is doing type
inference in the wrong place. The migration moves each such decision into
elaboration and records it in the Surface node.

## The representations

- **Syntax** is the proof as written: structure, names and literals as
  written, point selectors and resource clauses as written, and source
  locations. It holds no types, no resolved meanings and no kernel values.
- **Surface** is fully typed. Every semantic distinction the kernel makes is a
  required field: a comparison is native at a format, Integer, pointer,
  address, algebraic, Bool or float; an operation is machine at a format or
  Integer (`Subtract { kind: Machine(Int32) | Integer, left, right }`); a
  literal has its type; a name says what it binds; a generic call names its
  instance. Each operation has one form. Program expressions are Surface
  forms shared by C, C++ and Rust. Surface holds no internal identities and no
  kernel values: it names things as source does (`foo`, `p->rb_left`,
  `old(x)`, `statement(2).exit`), and need not be efficient.
- **Kernel** is the compact form for checking: variables, addresses, memory
  states, interned subterms. It holds no strings.

Surface to Kernel is many to one: `old(x)` and `at(function.entry, x)` lower
to the same term. Kernel to Surface must never be: two kernel terms that
differ, such as a native and an Integer comparison, never share a Surface
term. The [raise-lower principle](../docs/internals/raise-lower-principle.md)
is then about Kernel and Surface alone: raising transcribes, and lowering
reads what Surface says.

## Current state

Click's trees today, `SurfaceProposition` (19 variants) and `SurfaceTerm` (48
variants, with 10 more in `ResourceSubject`), are what the parser produces and
what lowering reads. They are Syntax with extras mixed in:

- They leave these distinctions implicit:
  1. comparison kind (`SurfaceProposition::Comparison { left, operator, right }`);
  2. arithmetic kind and format (`SurfaceTerm::Subtract(left, right)` and its
     siblings);
  3. literal type (`SurfaceTerm::IntegerLiteral(String)`);
  4. which binding a bare name means (`SurfaceTerm::Binding`);
  5. a generic call's instance.
- They embed the kernel's own program-expression type,
  `SurfaceTerm::ProgramExpression(ProgramExpression)`, with 42 variants of its
  own. An operation therefore has two spellings, such as `SurfaceTerm::Subtract`
  and `ProgramExpression::Subtract`, which lowering treats differently, and
  Surface holds kernel values (`ProgramExpression::Value` carries
  `MachineTerm`s; `Field` and `CUnary` keep a `lowered` kernel form).
  `ProgramExpression` serves C, C++ and Rust alike; names such as `QualifiedC`
  and comments calling it a C fragment date from when Click verified only C.
- Inference runs twice. Validation (`src/surface/validation/`) infers types to
  check the tree and mostly discards them; declaration expansion keeps some,
  such as method resolution (`design/typed-method-resolution.md`). Lowering
  (`src/surface/lowering/annotations.rs`) infers them again from context, with
  `contract_expression_is_integer`, `contract_expression_click_type`,
  `contract_expression_is_algebraic`, `enum_program_value_type` and
  `contract_pointer_element_type`, and by which lowering function a caller
  uses (`lower_contract_expression_to_spec` makes `Subtract` machine
  subtraction, `lower_contract_integer_to_spec` makes it Integer
  subtraction). Lowering is not compositional.
- The parser does some type-driven work as it reads: struct types, typedefs
  and parameter types.
- Because the kind is settled only inside lowering, the raiser must choose text
  that lowering will reinterpret as the kind it started from. It does so with
  special cases in `src/surface/proof/surface_synthesis.rs` (`spells_integer`,
  `machine_spelling_lowers_to_integer`, `is_signed_variable_arithmetic32`, the
  `uint32` arithmetic cast, `integer_observation_comparison`'s ascription).
  Each covers cases seen so far; together they cannot be complete.
- "Elaboration" currently names the Surface-to-kernel bridge
  (`SpecElaborationContext`), which this design calls lowering.

The old names `ClickProposition` and `ContractExpression`, aliases of
`SurfaceProposition` and `SurfaceTerm`, were removed with this design.

## Migration

Today's trees become Syntax. The typed Surface is designed fresh, small, and
built up one construct at a time. Each stage is its own pull request and leaves
every test passing.

1. **Name Syntax.** Rename today's `SurfaceProposition` and `SurfaceTerm` to
   `SyntaxProposition` and `SyntaxTerm`. A mechanical rename with no behavior
   change.
2. **Introduce Surface with comparisons and arithmetic.** Add the typed
   `SurfaceProposition` and `SurfaceTerm`, with required comparison and
   arithmetic kinds. While other constructs are not yet migrated, Surface
   carries them as a transitional `Untyped(SyntaxTerm)` node that lowering
   handles the old way. Elaboration produces Surface from Syntax; lowering reads
   the typed kinds and stops inferring them; the raiser fills them from the
   kernel term, and its guessing special cases for them are deleted.
3. **Program expressions.** Surface forms for program operations, shared by C,
   C++ and Rust, replacing the embedded kernel `ProgramExpression` and the
   `lowered` copies; Surface stops holding kernel values. Retire the C-only
   names.
4. **Literals.**
5. **Names:** a bare name says what it binds.
6. **Generic instances.**
7. **Finish.** Remove `Untyped`. Merge validation into elaboration and delete
   lowering's inference functions; lowering takes only Surface and is
   compositional. Rename `SpecElaborationContext`.

## Open questions

- **Point-dependent types.** Lowering's inference reads a local's type from
  the program state at a point (`c_variable_type`: entry values, locals,
  `local_type_state`). Stage 2 must establish what elaboration can know about
  a local's type before lowering, and record anything that depends on the
  point when the Surface term is formed at that point.
- **Abbreviation.** The printer needs one rule for when a cast or `to_integer`
  may be left out: exactly when elaborating the shorter text gives the same
  Surface term.
