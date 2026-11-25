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

## Every operation has its type

`int32` and `Integer` are different types, and a term's meaning includes the
type each operation works at and where each conversion happens. An int32
`a + b` wraps; an Integer `a + b` does not. `x == y` at int32 and
`to_integer(x) == to_integer(y)` hold in the same states but are different
terms, and a substitution or a tactic that works on one need not work on the
other: they are mathematically equal but not tactically interchangeable.

So Surface records every operation's type and every conversion as a node,
elaboration fills them from context, and lowering builds exactly that term.
The e-graph depends on it: congruence is sound only when each node names one
exact operation, and an equality class holds terms of one type, connected to
another type only through explicit conversions. An equivalence across types
is proved by checking, never applied by lowering.

Today the kernel's logical lowering breaks this for machine comparisons over a
compound operand: a spec's int32 `a + b == c` becomes
`IntegerEqual(observe(a + b), observe(c))`
(`condition_for_operand_views_in` in `src/kernel/machine_integer/comparison.rs`),
while the same C condition is `Compare { Int32, a + b, c }`. The raiser's
int32 and uint32 casts (`synthesize_int32_operand`,
`synthesize_uint32_operand`, `is_signed_variable_arithmetic32`) exist to steer
lowering back to the machine comparison. Fixing lowering removes them.

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
  `OldMachineTerm`s; `Field` and `CUnary` keep a `lowered` kernel form).
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

The migration reorganizes where decisions are made; it does not change what
they decide. Each step keeps the verifier's behavior: the same proofs pass, the
same kernel terms are produced, the same text is printed. A behavior change
joins a step only when today's behavior cannot be expressed in the new model,
and the step then names it. Where today's behavior is merely awkward, Surface
describes it as it is and the awkwardness is recorded for separate work. For
example, the kernel lowers a written int32 comparison over a compound operand
to an Integer comparison of observations
([Every operation has its type](#every-operation-has-its-type)); Surface
records that comparison's kind as elaboration chooses it today, and the
raiser's casts stay until that lowering is changed on its own.

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

## Stage 2 shapes

Surface records the kind the kernel distinguishes, using the kernel's own
format enums:

```rust
pub enum ComparisonKind {
    Machine(MachineIntegerType), // OldConditionTerm::Compare at a format
    Integer,                     // IntegerLessThan .. IntegerNotEqual
    Pointer,                     // PointerEqual
    Address,                     // AddressEqual: address(p) == address(q)
    Algebraic,                   // AlgebraicEqual
    Bool,                        // BoolEqual
    Float(KernelFloatType),      // Float32, Float64
}

pub enum ArithmeticKind {
    Machine(MachineIntegerType), // OldMachineTerm::Binary at a format
    Integer,                     // IntegerTerm::Add, Subtract, ...
}

SurfaceProposition::Comparison { kind: ComparisonKind, left, operator, right }
SurfaceTerm::Binary { op, kind: ArithmeticKind, left, right }
SurfaceTerm::Negate { kind: ArithmeticKind, operand }
SurfaceTerm::Untyped(SyntaxTerm) // transitional, until every construct is typed
```

Bitwise operators and shifts exist only on machine words, so their kind is
always `Machine(format)`. A 32-bit equality is one kernel fact at either
signedness (rule K6); `Machine(Int32)` and `Machine(UInt32)` equalities lower
to the same term, which Surface-to-Kernel's many-to-one direction allows.

- **Elaborate** fills each kind with the rules lowering uses today, moved, not
  changed, so behavior stays the same: the expected-type rules of
  `docs/reference/language/index.md`, with operand types from the typing
  environment.
- **Lower** reads the kind: a `Machine` comparison or operation lowers its
  operands as machine words at that format, an `Integer` one as Integers. No
  operand inspection, no caller-dependent path.
- **Raise** copies the kind from the kernel term: `OldConditionTerm::Compare
  { format, .. }` gives `Machine(format)`, `IntegerEqual` gives `Integer`,
  `OldMachineTerm::Binary { format, .. }` gives `Machine(format)`, an
  `IntegerTerm` operation gives `Integer`.
- **Print** writes `to_integer(...)` or a cast exactly where the kind differs
  from what elaborating the bare text would infer. It asks the one function
  elaboration uses for that inference, so printing and elaboration cannot
  disagree.

## Stage 2 progress

Comparisons are typed first. `src/surface/typed_surface.rs` holds
`SurfaceProposition::Comparison { kind, left, operator, right }` with
`ComparisonKind::{Native, Integer, Algebraic, Sequence}`; operands are still
`SurfaceTerm::Untyped`. `elaborate_comparison`
(`src/surface/lowering/annotations/comparison_elaboration.rs`) chooses the
kind, with the rules lowering used, and also expands a struct equality into
its fields' equalities; `lower_surface_proposition` reads the kind and
inspects no operand.

`Native` stands for the shapes listed above as `Machine(format)`, `Pointer`,
`OldAddress`, `Bool` and `Float`. Which of these a native comparison is, and its
format, is the C type of its operands, built bottom-up from them; that is
compositional, so lowering may compute it. It becomes a recorded field once
program expressions are typed Surface (stage 3). The kind elaboration records
now is the top-down decision: whether a written comparison is native, Integer,
algebraic or sequence, which depends on both operands at once.

Still to do in stage 2: elaboration runs where lowering reaches a comparison,
not as a pass before lowering; the raiser still returns Syntax and keeps its
guessing special cases; and arithmetic kind is still chosen by which lowering
function the comparison's kind calls.

## Open questions

- **Point-dependent types: answered.** Lowering's lookup (`c_variable_type`)
  reads only declared types: the function's result type, a resolved
  binding's type, parameters' declared types and entry values, locals at
  entry, and a state's local object types. A C local's type never changes as
  the program runs. What depends on the point is only which locals are in
  scope there, through blocks and shadowing. So elaboration needs a typing
  environment for the proof's position: the declared parameters and the
  locals in scope at it. In an execution proof that position is the step's
  frontier, so a proof statement is elaborated when its step is reached,
  still once and before lowering.
- **Abbreviation.** The printer needs one rule for when a cast or `to_integer`
  may be left out: exactly when elaborating the shorter text gives the same
  Surface term.
