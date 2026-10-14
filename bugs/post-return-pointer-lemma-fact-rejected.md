# An accepted pointer lemma application fails return-fold certification

A checked lemma application must preserve the justification of its resulting
fact when a later return-resource fold is certified. The rotation proof accepts
an application of the imported `sized_parent_is_shape` theorem after the C call,
then its final certification rejects the equality that application introduced.
The provider theorem independently verifies in `rbtree_size_model.click`.

Reproduce from the repository root:

```
click verify examples/rbtree-augmented/rbtree_size_model.click
click verify --trace-proof sized_rotate_restores_subtree_size_left bugs/rbtree-return-fold-repro.click
```

The second command refuses an introduced equality between
`sized_parent_is(Node(...), parent)` and
`rb_parent_is(sized_shape(Node(...)), parent)`. Its pointer argument prints as
an `array-ref<int32>` in the initial empty snapshot. The checked trace shows the
application and its admitted equality before final return-fold certification
reports `return proof assumes an unjustified path fact`.

The positive rotation example instead unfolds the small parent predicates
locally and verifies both directions and all child configurations. Smaller
scalar-pointer examples with imported lemma applications after a void return,
including execution theorems, verify; the problem has not been reduced to all
post-return applications. Preserve the original struct-pointer/model arguments
and contract scope in the regression.

Acceptance: identify which checked source or argument instantiation is lost,
retain the checked justification through final certification, and cover the
original pointer/model application with a positive regression. Do not accept
arbitrary introduced path facts. Remove this report and its draft companion
when the fix and regression land.
