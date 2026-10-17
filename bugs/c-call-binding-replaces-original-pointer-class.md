# C call binding replaces the actual pointer's original class

Soundness: soundness-adjacent. Binding a cast pointer argument supplies the callee's declared pointee class in place of the caller's existing class. This breaks the original-class invariant. With the in-progress nominal model-field typing, an incompatible pointer can consequently enter a model field through a checked C contract. No false scalar program claim has been demonstrated on the baseline.

`bind_c_function_arguments` and `bind_c_contract_arguments` both finish coercion with `.with_pointer_object_class(parameter.pointee_class())`. Coercion must retain the actual pointer's original class, including across a `void*` formal; a declaration cannot establish a different original class.

Reproduction: `mdtests/model_pointer_c_calls_reject_changed_class.md`, with the matching-type control in `mdtests/model_pointer_c_calls_keep_original_class.md`. Before the repair, both verify. The negative case must be refused while the control continues to verify. The regression depends on the nominal model-field work in the same branch; the overwrite itself is present on upstream.

Acceptance: preserve the actual class in both checked-body and contract argument binding; establish positive formal-input evidence only from the written contract's declared requirements. Cover differing classes, unknown classes, null, and class preservation through `void*` without rescanning unrelated state.
