# A pure function or predicate that reads a C global carries no memory, so its facts survive stores to that global

## Violated invariant

A pure function application and a predicate fact must denote a value of the
memory state they are evaluated in. The kernel keys an application
`ClickFunctionApplication { name, arguments }` and a predicate fact
`Proposition::Predicate { name, arguments }` on their *arguments* only; the
only memory an argument can carry is the snapshot inside a
`SpecPureFunctionArgument::ArrayRef` / `SpecPredicateArgument::ArrayRef`
(`src/kernel/spec.rs`, `evaluate_spec_pure_function_argument_paths_in` around
line 7298 and `lower_spec_predicate_proposition_at_state_in` around line 5624,
which pushes `Term::CMemory` only for `ArrayRef` arguments). The surface lets
a function or predicate body name a file-scope C object by its bare name, and
`lower_c_binding_to_spec` (`src/surface/lowering/annotations.rs:6062`) lowers
that name to a `SpecExpression::MemoryLoad` of the ambient memory. Nothing in
the application term records that memory, so `read_counter(0)` before and
after `counter = counter + 1` is the same kernel term and a `requires` fact
about it is reused verbatim at the `ensures`.

The surface classification `memory_independent_click_functions` /
`contract_expression_reads_memory` (`src/surface.rs`, near line 5897) also
treats `CBinding(_)` and `CFragment(CExpression::Variable(_))` as reading no
memory, so such a function is registered as memory-independent and its
array-ref arguments (if any) are anchored to `value_independent_click_memory()`
as well. The kernel trusts both.

## Reproduction

```c filename=bump.c
int32 counter = 1;

int32 bump() {
    counter = counter + 1;
    return counter;
}
```

```click
verifying "bump.c";

function read_counter(x: int32) -> int32 {
    counter + x
}

int32 bump() {
    owns &counter[0..1];
    requires counter == 5;
    requires read_counter(0) == 5;
    ensures counter == 6;
    ensures read_counter(0) == 5;
} by {
    execute();
    simp();
}
```

Observed: `1 selected proof verified`, exit 0. `read_counter(0)` is
`counter + 0`, which is 6 at exit, so `ensures read_counter(0) == 5` is false.
Both postconditions verify together, so the proof context is inconsistent with
the function's own definition (an `unfold(read_counter(0))` in the same proof
yields `read_counter(0) == load(&counter) + 1`).

The predicate form is the same bug through `Proposition::Predicate`
(same C file):

```click
predicate counter_is(v: int32) {
    counter == v
}

int32 bump() {
    owns &counter[0..1];
    requires counter == 5;
    requires counter_is(5);
    ensures counter == 6;
    ensures counter_is(5);
} by {
    execute();
    simp();
}
```

Observed: `1 selected proof verified`, exit 0.

A variant `ensures read_counter(0) == old(read_counter(0))` with no
`requires` about the application also verifies (by reflexivity of the
structurally identical terms) although the body stores to `counter`.

Adding an array-ref parameter whose cell the body also reads
(`function f(p: int32[], x: int32) -> int32 { counter + x + p[0] }`) makes
the classification memory-dependent, the array ref carries the snapshot, and
the false `ensures` is refused; the bug needs a body whose only memory read is
a bare global name, or a function/predicate with no array-ref parameter at all.

## Intended regression

Both repro files above as `fail`-expected mdtests (`ensures read_counter(0)
== 5` and `ensures counter_is(5)` must be refused), plus a positive twin in
which the function reads the global and the `ensures` restates the *entry*
value through `old(read_counter(0)) == 5`, which must still pass.

## Acceptance criteria

- A pure function or predicate whose body reads a file-scope C object is
  not classified memory-independent (`contract_expression_reads_memory` must
  treat a `CBinding`/`CFragment(Variable)` that resolves to a global object as
  a memory read), and its application/fact carries the memory it reads in,
  e.g. an explicit memory argument, so that the term differs across a store
  to the object; or the surface refuses bodies that read globals.
- The kernel side should not depend on the surface for this: either the
  lowered application must carry a memory term whenever the lowered body
  contains a `MemoryLoad` (`register_kernel_pure_function_definitions` can
  see it), or the kernel refuses to lower an application/predicate of a
  registered memory-reading body without a memory argument.
- `requires read_counter(0) == 5` must not establish `ensures read_counter(0)
  == 5` across `counter = counter + 1`; `old(read_counter(0))` must remain
  available and distinct from the current application.
