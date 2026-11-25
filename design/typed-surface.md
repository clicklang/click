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

## The representations

- **Syntax** is the proof as written. It may be missing anything inference
  supplies: a comparison's kind, an operation's format, a literal's type, which
  binding a name means, a generic call's instance.
- **Surface** is fully typed. Every semantic distinction the kernel makes is a
  required field: a comparison is native at a format, Integer, pointer,
  address, algebraic, Bool or float; an operation is machine at a format or
  Integer; a literal has its type; a name says what it binds; a generic call
  names its instance. Surface holds no internal identities: it names things
  as source does (`foo`, `p->rb_left`, `old(x)`, `statement(2).exit`), and
  need not be efficient.
- **Kernel** is the compact form for checking: variables, addresses, memory
  states, interned subterms. It holds no strings.

Surface to Kernel is many to one: `old(x)` and `at(function.entry, x)` lower
to the same term. Kernel to Surface must never be: two kernel terms that
differ, such as a native and an Integer comparison, never share a Surface
term. The [raise-lower principle](../docs/internals/raise-lower-principle.md)
is then about Kernel and Surface alone: raising transcribes, and lowering
reads what Surface says.

## Current state

Click's trees today, `SurfaceProposition` and `SurfaceTerm`, are what the
parser produces and what lowering reads. They are between Syntax and
Surface:

- They leave these distinctions implicit:
  1. comparison kind (`SurfaceProposition::Comparison { left, operator, right }`);
  2. arithmetic kind and format (`SurfaceTerm::Add` and its siblings);
  3. literal type (`SurfaceTerm::IntegerLiteral(String)`);
  4. which binding a bare name means (`SurfaceTerm::Binding`);
  5. a generic call's instance.
- Inference runs twice. Validation (`src/surface/validation/`) infers types to
  check the tree and mostly discards them; declaration expansion keeps some,
  such as method resolution (`design/typed-method-resolution.md`). Lowering
  (`src/surface/lowering/annotations.rs`) infers them again from context, with
  `contract_expression_is_integer`, `contract_expression_click_type`,
  `contract_expression_is_algebraic`, `enum_program_value_type` and
  `contract_pointer_element_type`, and by which lowering function a caller
  uses (`lower_contract_expression_to_spec` or
  `lower_contract_integer_to_spec`).
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

## Migration

Each stage is its own pull request and leaves every test passing.

Today's `SurfaceProposition` and `SurfaceTerm` keep their names and become
the typed Surface. The parser gets a type of its own.

The old names `ClickProposition` and `ContractExpression`, aliases of
`SurfaceProposition` and `SurfaceTerm`, were removed with this design.

1. **Introduce Syntax.** Add `SyntaxProposition` and `SyntaxTerm` as the
   parser's output, initially the same shape as today's Surface types, with an
   `elaborate` step converting Syntax to Surface. No behavior change.
2. **Type comparisons and arithmetic.** Give Surface comparisons and arithmetic
   required kinds. Elaboration fills them from Syntax, lowering reads them
   instead of inferring them, and the raiser fills them from the kernel term.
   Delete the raiser's guessing special cases for these kinds.
3. **Literals.**
4. **Names:** a bare name says what it binds.
5. **Generic instances.**
6. **Merge validation into elaboration.** Delete lowering's inference
   functions; lowering takes only Surface. Rename `SpecElaborationContext`.

## Open questions

- **Point-dependent types.** Lowering's inference reads a local's type from
  the program state at a point (`c_variable_type`: entry values, locals,
  `local_type_state`). Stage 2 must establish what elaboration can know about
  a local's type before lowering, and record anything that depends on the
  point when the Surface term is formed at that point.
- **Abbreviation.** The printer needs one rule for when a cast or `to_integer`
  may be left out: exactly when elaborating the shorter text gives the same
  Surface term.
