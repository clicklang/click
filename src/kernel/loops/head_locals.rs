use super::*;

/// The changed scalar portion of an arbitrary iteration's local environment.
/// Choose every value and its storage from the immutable entry state before
/// constructing any successor. Unselected locals remain shared with entry.
pub(super) struct LoopHeadLocals<'a> {
    entry: &'a ExecutionState,
    values: Vec<LoopHeadLocal>,
}

struct LoopHeadLocal {
    name: BindingName,
    program_type: ProgramType,
    value: ProgramValue,
    slot: Option<Pointer>,
}

impl<'a> LoopHeadLocals<'a> {
    pub(super) fn new(
        entry: &'a ExecutionState,
        names: BTreeSet<BindingName>,
        variables: &mut KernelVariableGenerator,
        budget: &mut ExecutionBudget,
    ) -> ExecutionResult<Self> {
        let mut values = Vec::new();
        for name in names {
            // Globals are represented by memory alone. Uninitialized objects,
            // arrays and aggregates do not have a scalar value to abstract.
            let Some(LocalBinding::Object { program_type, .. }) = entry.locals.binding(&name)
            else {
                continue;
            };
            let program_type = *program_type;
            let Some(value) = fresh_loop_local_value(program_type, variables, budget)? else {
                continue;
            };
            // These are loop-interface requirements: the back edge checks
            // that a pointer returns to this subobject and object class.
            let value = with_retained_extent(value, entry.locals.get(&name));
            let value = with_retained_object_class(value, entry.locals.get(&name));
            let slot = entry
                .locals
                .slot(&name)
                .filter(|pointer| entry.memory.has_block(&pointer.block))
                .cloned();
            values.push(LoopHeadLocal {
                name,
                program_type,
                value,
                slot,
            });
        }
        Ok(Self { entry, values })
    }

    /// Compatibility adapter for the existing memory representation. It still
    /// records stores; this is not the logical execution of a loop iteration.
    /// Keep that mechanism here, separate from choosing the loop-head values,
    /// until memory can construct the abstract local cells directly.
    pub(super) fn install(self) -> ExecutionState {
        let mut state = self.entry.clone();
        for local in self.values {
            if let Some(slot) = local.slot {
                state.set_memory(state.memory.clone().store(slot, local.value.clone()));
            }
            state
                .locals
                .set_typed(local.name, local.value, local.program_type);
        }
        state
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn head_locals_keep_entry_and_construct_matching_stack_cells() {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = Memory::local_pointer("changed");
        let entry = ExecutionState::new()
            .with_local("changed", int32(3))
            .with_local("retained", int32(7))
            .with_local("logical", int32(9))
            .with_memory(
                Memory::new()
                    .with_block(slot.block.clone(), 4)
                    .store(slot.clone(), int32(3)),
            );
        let before = entry.clone();
        let description = LoopHeadLocals::new(
            &entry,
            BTreeSet::from(["changed".into(), "logical".into(), "absent".into()]),
            &mut KernelVariableGenerator::fresh_for_execution(BTreeSet::new()),
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        assert_eq!(entry, before);
        let head = description.install();
        assert_eq!(entry, before);
        assert_ne!(head.locals.get("changed"), entry.locals.get("changed"));
        assert_ne!(head.locals.get("logical"), entry.locals.get("logical"));
        assert_eq!(head.locals.get("retained"), entry.locals.get("retained"));
        assert_eq!(
            head.memory.load(&slot),
            ExpressionOutcome::Value(head.locals.get("changed").unwrap().native().into_owned())
        );
        assert!(
            !head
                .memory
                .has_block(&Memory::local_pointer("logical").block)
        );
        assert!(head.locals.get("absent").is_none());
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/loops/head_locals.rs");
    }
}
