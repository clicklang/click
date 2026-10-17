# Model constructor synthesis drops a checked void-pointer cast

Soundness: not soundness. The checker rejects the ill-typed generated rewrite;
this prevents a valid proof from being synthesized, and establishes no false claim.

A call exports `held.model == Model::At((void*)kid)`, where `At` has a `void*`
field and the C parameter is a struct pointer. The equality is retained and
`assumption()` can check it when spelled explicitly. However, `simp()` cannot
establish `held.model != Model::Empty`: source reconstruction of the selected
model equality spells `Model::At(kid)`. Its constructor argument has the wrong
carrier type, so the reconstructed premise does not lower to the checked fact.

Reproduction and positive pure-theorem control:
`mdtests/model_pointer_address_constructor_preserves_cast.md`. The original
call trace admitted the model equality, then reported zero of one selected
premises had a checked source spelling. Adding an explicit `have` of the casted
equality made the original caller verify, confirming the source synthesis gap.

Acceptance: preserve the cast when synthesizing the constructor; the unchanged
C caller verifies, its `simp()` expansion verifies as source, and nominal model
pointer fields retain their stronger original-object requirements.

Working-tree fix and regression added; not yet published.
