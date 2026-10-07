# A loaded tagged null word cannot convert back to a pointer

## Violated invariant

An owned unsigned-long load known to equal 1 has no non-null pointer origin,
but clearing its two low tag bits yields zero and must be convertible to the
canonical null pointer. The corresponding literal case already verifies in
`mdtests/tagged_pointer_null_word.md`.

## Reproduction

Save the following as `erase-word.c` and `erase-word.click`, then run
`click verify erase-word.click`:

```c
struct node { unsigned long word; };
struct node* parent(struct node* node) {
    unsigned long pc = node->word;
    return (struct node*)(pc & ~3);
}
```

```click
verifying "erase-word.c";
struct node* parent(struct node* node) {
    owns node->word;
    requires node->word == 1;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

Observed on 2026-10-07: `integer-to-pointer cast requires a value that is a
recorded pointer address or zero`. This blocks the unchanged Linux
`__rb_erase_augmented` at `parent = __rb_parent(pc)` when erasing a black
root leaf. No C erase contract has been delivered yet.

## Intended regression and acceptance

Add the loaded-word case beside the existing tagged-null fixture and require
it to pass. Also check a loaded word known to equal zero and reject a word
whose masked value is nonzero without pointer provenance. Preserve the
existing pointer-origin rules; integer equality with a non-null address must
not create provenance. Check the null fast path in
`src/kernel/eval/expression.rs::cast_c_value_to_type`, which currently tests
only `uint64_as_const()`, and the tagged-address resolver.
