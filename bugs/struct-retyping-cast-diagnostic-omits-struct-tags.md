# A struct retyping cast diagnostic omits the struct tags

## Violated invariant

A diagnostic must say what is wrong in terms the C author can act on. The
refusal of a pointer cast that changes the pointed-to struct names two
different types, but it prints both as the same kernel type, so the message
contradicts itself.

`Parser::validate_pointer_cast` in `src/languages/c/syntax.rs` compares the
pointer type and, separately, the struct name. A pointer to a struct is a
`C0Type` such as `Int32PointerPointer` with the tag kept beside it. When only
the tags differ, the message prints the two `C0Type` values with `{:?}` and
drops the tags.

## Reproduction

```c
struct a { int32 x; };
struct b { int32 y; };
struct b **as_b(struct a **p) { return (struct b **)p; }
```

`syntax::parse_functions` refuses it, correctly, with:

```
incompatible C pointer types: retyping object-pointer casts are unsupported; expected Int32PointerPointer, got Int32PointerPointer
```

The same happens one level down, for `(struct b *)p` with `struct a *p`, and
the message also leaks the internal type name where the source wrote a C
type.

## Intended regression

A test in `src/languages/c/tests.rs` that parses the reproduction and checks
that the refusal names both C types, for example
``expected `struct b **`, got `struct a **` ``, and still says that retyping
object-pointer casts are unsupported. Cover the one-level case too.

## Acceptance criteria

- Both struct-retyping refusals in `validate_pointer_cast` print the source
  types with their struct tags and pointer depth.
- Casts that differ in the pointer type itself still name both types.
- The existing `mdtests` that expect `retyping object-pointer casts are
  unsupported` still pass.
