# Mathematical integers

`Integer` is Click's exact, signed mathematical number type for
specifications. It is separate from every C integer type and has no C storage,
ABI, machine width, or implicit runtime allocation. The kernel and standard
library may represent it internally in implementation-specific ways, but the
surface contract below is stable.

## Type and conversions

The public name is `Integer`; there is no `Int` alias. Existing `int` remains
the C `int32` type. Integer literals are arbitrary-size mathematical values
when their context is `Integer`. Machine values and Integer values do not mix
implicitly.

An unused `Integer` parameter does not reinterpret a separately machine-typed
literal or expression. Expected-type propagation follows the expression and
its binding context; it does not leak across unrelated clauses.

`to_integer(x)` accepts each supported signed or unsigned machine-integer type
and preserves its numeric value. Signed `-1` and unsigned `4294967295u32` are
therefore different Integer values. Converting an already evaluated machine
value is total, but evaluating the argument retains all of its C definedness
obligations. In particular, `to_integer(x + 1)` does not discharge an
overflow obligation for `x + 1`.

Reverse conversions are destination-specific: `to_int8`, `to_int16`, `to_int32`,
`to_uint8`, `to_uint16`, `to_uint32`, `to_int64`, and `to_uint64`. A conversion
requires proof that the Integer lies in the destination's exact range. It does
not truncate, wrap, saturate, or insert an unchecked assumption. A symbolic
conversion requires both bounds, even in a reflexive proposition.

The same rule applies to conversions between `Nat` and `Integer`. `Nat` to
`Integer` is total; `Integer` to `Nat` requires a nonnegative proof. Checked
round-trip and arithmetic laws relate the types without identifying them by
implicit coercion. `Nat` remains the structural, nonnegative datatype used by
its own induction theorems.

`to_integer(a + b)` and `to_integer(a) + to_integer(b)` are distinct
expressions. A signed machine-addition equality needs evidence that the C
operation is defined; an unsigned equality must account for modular arithmetic.
No unconditional conversion distribution rule is sound.

## Exact operations and definedness

Integer literals, unary negation, addition, subtraction, multiplication,
equality, disequality, and order comparisons are supported. Exact Integer
arithmetic does not overflow. Bitwise operations remain machine operations.

Division and remainder are deliberately deferred from the current supported
surface, but their semantics are settled for a future implementation. They use
Euclidean division: for nonzero `d`,

`a == (a / d) * d + a % d` and `0 <= a % d < abs(d)`.

Thus `-7 / 3 == -3` and `-7 % 3 == 2`; this is distinct from C's truncation
toward zero. A zero divisor is a definedness obligation.

Every checked conversion and every future checked division must establish its
definedness in the current proof context before a theorem or execution
certificate is accepted. Evaluation facts are not arbitrary assumptions.

A statement whose evaluation condition is not established where the statement is
written is refused as it is lowered, and the refusal is written for whoever wrote
the statement. It names the clause or expression, the written subterm whose
evaluation raised the condition, and the condition as a requirement in the
reader's own names -- the four bytes at `p[hi - 1]` must be viewable, `hi - 1`
must not overflow, an `Integer` must fit the machine type it is converted back
to. It says how many of that evaluation's conditions the premises did establish
and names them, lists the premises it consulted in source spelling (a premise
that is a conjunction counted as its conjuncts, bounded like every other fact
list), says why a viewability premise over a wider range did not settle a single
cell, and gives one repair: the cell's own viewability as a one-element range,
the operation's `defined(...)`, or the converted value's bounds. Where the
premise set it consulted was empty, it says so rather than implying a premise
was read and rejected. A `.click` clause carries no source span, so the refusal
says that too instead of leaving a reader hunting for a line number.

Capturing an Integer expression as one symbolic term follows the same rule.
A partial machine operation inside the expression -- the `hi - 1` of a fold
range `(lo..(hi - 1))`, for instance -- makes the captured value the value of
only one evaluation path, guarded by that operation's definedness condition.
The capture is accepted when the proof context already states that condition
by an exact route, because then the guarded path is the only live one and
admitting the condition adds nothing to what the captured term asserts. It is
refused when the condition is not available, and the refusal names the
offending subterm -- the fold's range endpoint, initializer, or body -- along
with the condition that is missing. A missing condition is never dropped.

## Specification coverage

Integer is supported in:

- specification bindings, typed `let` bindings, and contextual literals;
- universal and existential quantifiers over the unbounded domain;
- pure function parameters and results, and theorem parameters and claims;
- datatype fields and generic type arguments;
- resource model fields and resource pattern bindings;
- typed range-fold accumulators, endpoints, and bodies; and
- mixed C/Integer propositions where every boundary is explicit and checked.

Existing binders, function syntax, match syntax, and fold syntax are reused.
Fold indices and accumulators have independent types: an `int32` index may read
C array elements while an `Integer` accumulator computes an exact sum. Empty
and reversed range behavior is unchanged, and fold initial values and bodies
must have one accumulator carrier.

Quantifier domains remain logically unbounded. Finite enumeration is only a
bounded proof technique. Universal introduction and existential witnesses use
capture-avoiding substitution, preserve carrier identity, and retain any
definedness obligations in the witness or proposition. Deep repeated universal
introduction has a known quadratic cost and is deferred for targeted scaling
work; correctness checks and existing budgets remain in force. See the
[deep quantifier scaling issue](https://github.com/clicklang/click/blob/master/issues/deep-quantifier-scaling.md).

For an existential witness, definedness remains attached to that same witness.
It cannot be weakened into an implication whose guard is false, since that
would permit an irrelevant witness to establish the existential claim.

## Arithmetic automation and trust boundary

The supported arithmetic automation is linear: addition, subtraction, order,
and multiplication by constants, together with explicit machine-conversion
and checked C-arithmetic laws. General multiplication is a valid Integer term,
but there is no promise of general nonlinear automation.

Arithmetic planning emits explicit, inspectable evidence. The kernel validates
operators, coefficients, terms, premises, and range claims independently;
zero-premise tautologies are valid, while sparse or altered premise indices
fail locally. Expansion prints ordinary proof steps, and ordinary verification
rechecks those steps without rerunning the planner. Profiling and audit use the
same checked boundary.

A bounded nonlinear rule is available explicitly: the `integer_product_bounds`
node in the special arithmetic family consumes four named constant-endpoint
inequalities for the two operands. Multiplication is monotone in each operand
when the other is fixed, with its direction set by that operand's sign; its
extrema on a rectangle therefore occur at the four corners. The kernel checks
those four exact products against the claimed constant lower or upper bound,
including intervals crossing zero. This does not extend the arithmetic planner
or reinterpret a machine product as an exact Integer product. The rule also
checks interval ordering, proposition polarity, references, operand identity,
and the selected conclusion.

Operand comparison uses shared Integer node identities. One node reads exactly
four premises; unused premises and deep operand subtrees do not increase its
checking work. Big-integer multiplication and comparisons are charged from the
numeric bit lengths before arithmetic starts. Deterministic regressions measure
node inventories, unused facts, operand depth, magnitude, and the work-budget
boundary. Pure Integer certificates round-trip and expand/reverify. A synthetic
unchanged C identity wrapper checks a mathematical machine-observer product range
across
verification, expansion/reverification, profiling, and retained audit.

Fold reasoning uses explicit empty-range and next-element laws. Fold terms are
opaque affine atoms in the bounded certificate fragment. The planner accepts
selected checked premises and explicit constant scaling; it does not enumerate
a symbolic range or invent an arithmetic assumption. The unchanged C
summation regression proves exact functional correctness with an `Integer`
prefix sum while separately proving that each machine addition is defined.

Both laws take the raw fold term, which forces a proof to retype the fold at
the proof site. `prove_integer_range_fold_over_equal_terms` restates either law
over a term the caller proves equal to the fold — in practice the opaque
application of the pure function whose declared body *is* that fold. Those
equalities are premises of the produced theorem, beside the law's own guards,
so the entry point assumes nothing the two laws do not already prove. The
append form instantiates the append law at the predecessor index `start..end -
1` and checks, against an empty fact context, that the law's
`fold(start..(end - 1) + 1)` and the caller's `fold(start..end)` are the same
fold by endpoint affine normalization; substituting the caller's term for the
equal shorter fold inside the next-element step is congruence under the second
premise. `integer_range_fold_predecessor_application` builds the predecessor
application so its int32 argument and that index agree by construction.

`substitute_integer_term_in_proposition` is the matching goal refresh. It is
Leibniz for a step that already holds the two terms' proved equality, so it is
deliberately shallow: it descends only the arithmetic spine — negation,
addition, subtraction, multiplication — and compares interned identity
everywhere else, never entering a range fold's binders. Rewriting only some
occurrences of an equal term is sound, and the walk stays linear in the
proposition it rebuilds.

## Sharing, scope, and identity

Integer expressions use immutable shared nodes. A chain of aliases such as
`a0 = x; a1 = a0 + a0; ...` must remain linear in source size rather than
expanding into an exponential arithmetic tree. Canonical nodes have stable,
shallow identities and traversals visit each reachable node once where the
operation permits.

Interning keys contain shallow child identities. Cache maintenance must not
rehash an unrelated large numeral repeatedly or retain dead expression graphs
indefinitely. Alpha keys serialize shared graphs with local child indices.
Renaming and substitution caches include lexical binder scope, and carrier
identities distinguish C values from Integer values.

Substitution and generic rewriting preserve shared arithmetic nodes. They do
not eagerly evaluate newly constant expressions: replacing a variable with a
large repeated-squaring DAG must not allocate an enormous numeral from a tiny
proof. A shared replacement is validated once and its shallow root is charged
at each occurrence.

Memory loads and fold atoms retain exact snapshot identity. Alpha-equivalent
loads from one retained snapshot may match; a different snapshot, body,
carrier, or definedness context does not. Snapshot identity is opaque to
arithmetic and is never inferred from a raw term identifier or fingerprint.

Endpoints are the one fold component compared up to equality rather than
identity. A range fold reads nothing but its endpoints, its initial value, and
its body, so two folds with the same initial value and the same body denote
the same Integer once their start endpoints are equal and their end endpoints
are equal. Endpoint equality is decided without any search over the ambient
facts: interner identity, an exact recorded equality between exactly those two
terms, or the two endpoints' affine normal form. The last route is what makes
`(hi - 1) + 1` and `hi` one endpoint, which is how an induction step carries
the append law's `end + 1` back to its goal; wrapping machine arithmetic makes
it exact, so it needs no ordering or definedness side condition. The body
remains exact, so a fold over a written array is never equated with the same
fold over the snapshot before the write.

## Shared machine constants

`MachineIntegerFormat` records signedness and one of the fixed widths 8, 16,
32, 64, or 128. `MachineIntegerConstant` pairs that format with a checked
two's-complement payload; its private fields prevent oversized payloads from
entering a consumer. The inclusive bounds, literal checking, numeric observation,
and conversion policies share this representation. Boolean values remain a
separate source type. Width gives the number of value bytes, not ABI alignment
or a promise that a frontend supports that width.

Checked conversion preserves the numeric value or refuses it. Modulo conversion
is a separately requested operation: it sign-extends a signed source, retains
an unsigned source's value, and reduces modulo the destination width. This
implements the constant policy of C++20 integral conversions and Rust integer
`as`; a C importer must still select its target's signed narrowing policy.
The ordinary reverse conversion from Integer always uses the checked operation.

The runtime machine types use the shared format for their bounds,
constant observations, Integer conversions, and constant rewrite normalization.
C++ literals use it as well. The runtime bridge requires an exact format match,
including signedness; narrow signed constants retain the
existing sign-extended 32-bit carrier. An arbitrary Integer larger than the
format is refused from its cached bit length before inspecting its limbs.
Parsing work scales with the explicitly written decimal spelling, and numeric
allocation is charged before constructing bounded exact values.

Signed and unsigned 128-bit constants, their full endpoint ranges, widening,
and narrowing are represented and tested against independent exact arithmetic.
The kernel also has a bounded wide scalar profile, described below. Source
`__int128` execution and surface `int128` / `uint128` types remain unsupported.

## Explicit machine modulo casts

The shared kernel `c_integer_cast_modulo` boundary implements Rust integer `as`
and C++20 integral conversions for the admitted 8–64-bit runtime types. It
checks the evaluated source and destination types, folds root constants through
`MachineIntegerConstant`, and retains symbolic operands in the common term
arena. Narrow signed results keep the existing sign-extended 32-bit carrier;
unsigned results retain the low destination bits. Widening uses source
signedness before the destination interpretation. Conversion construction
inspects only a bounded number of root nodes.

Boolean sources observe their normalized zero-or-one numeric value. Boolean
results, floats, pointers, arrays, and unsupported widths are refused at this
integer boundary; their ordinary conversions use their own rules. Evaluation
of the operand still carries its definedness obligations, including overflow.
This explicit policy does not relax ordinary C casts or checked Integer
conversions. Casts involving 128-bit values use `MachineIntegerCast`, retaining
both source and destination types. Constants fold through the same exact
format policy, and symbolic operands remain typed through substitution and
proof rewriting. The existing 8–64-bit casts keep their current carriers.

Wide integral widening and narrowing, including signedness changes, are
supported at the kernel's explicit modulo boundary. Ordinary C conversions
involving wide values retain the representable-range policy for signed
destinations: both lower and upper bounds must be established unless the
whole source range fits. Unsigned destinations use modulo conversion.
Neither route loses the operand's definedness obligations.

Exact Integer observation removes a widening cast only when every value of
the source type fits the destination. Narrowing and signedness changes that
can change the numeric value stay machine observations of the converted
value; they are not equated with the source's mathematical Integer.

## Wide runtime scalars

The shared kernel has `CType::Int128` / `UInt128` and corresponding `CValue`
wrappers in the existing machine-term arena. `c_int128_literal` and
`c_uint128_literal` retain all 128 bits in `MachineIntegerConstant` payloads.
Symbolic variables, scalar locals, assignment, function parameters/results,
and substitution preserve the wide type. The pinned x86_64 Linux profile gives
these scalar objects 16 bytes and alignment 16; value width alone does not
choose an arbitrary target's ABI alignment.

Exact Integer observation retains the source's wide machine type and numeric
interpretation. Reverse Integer conversions use the full signed/unsigned
bounds and retain both obligations for symbolic inputs. Truthiness compares
that exact observation with zero, including high bits above bit 63. These
observations do not turn native arithmetic into unbounded Integer arithmetic.

A wide runtime wrapper accepts only a matching wide constant, a symbolic
variable, the shared checked Integer-to-machine node, or a typed machine cast
for that destination.
Legacy word constants and arithmetic nodes cannot acquire 128-bit semantics
by retagging their wrapper. Validation examines the root and any strictly
widening conversion chain (bounded by the five machine widths); substitutions,
alpha keys, snapshot identities, and bounded walks keep the full payload.

This profile does not yet admit native wide arithmetic,
wide pointer/array types, aggregate field access,
byte loads, callbacks, or any C/C++/Rust source spelling. Internal C0 type
identities preserve the kernel sorts without adding parser admission. The
frontends continue to reject reachable `__int128` behavior. Checked
multiplication, storage access, and source admission are later slices;
existing implementation fixtures remain unchanged.

## Work budgets and certificate scaling

Numeric work has two independent costs: reachable expression visits and
magnitude-dependent arithmetic work, including numeric bit length. A numeric
operation consumes the active verification budget before doing the operation.
Lowering also checks the configured simple-operation allowance. A counter added
after arithmetic is insufficient, and a weighted charge must not be simulated
by a loop of unit checkpoints.

Shared DAG traversals, substitution, alpha comparison, certificate checking,
and snapshot matching must scale with the selected expression and certificate,
not unrelated proof state. Premise references are explicit and checked before
storage allocation. Large constants do not silently truncate, and enormous
mathematical ranges do not trigger uncontrolled enumeration.

The trust boundary is independent kernel checking of the resulting proof
object and certificate. C source remains the verification boundary: the
unchanged summation program is the regression, and proof authors must not add
no-op C branches, proof-only locals, helper rerouting, or renamed identifiers
to make an Integer proof succeed.

## Related references

- [Kernel implementation](kernel.md)
- [Verification efficiency](verification-efficiency.md)
- [Memory derivation DAG](memory-dag.md)
- [Language reference: mathematical integers](../reference/language/index.md#mathematical-integers)
- [Canonical unchanged-C summation regression](https://github.com/clicklang/click/blob/master/mdtests/integer_sum_range_fold.md)
- [Missing element-bound regression](https://github.com/clicklang/click/blob/master/mdtests/integer_sum_range_fold_missing_bounds.md)
- [Intermediate-overflow regression](https://github.com/clicklang/click/blob/master/mdtests/integer_sum_range_fold_intermediate_overflow.md)
- [Endpoint congruence regression](https://github.com/clicklang/click/blob/master/mdtests/fold_endpoints_rewrite_under_equality.md)
- [Endpoint congruence refusal](https://github.com/clicklang/click/blob/master/mdtests/fold_endpoints_reject_a_different_body.md)
