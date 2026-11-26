//! Structural pointer rewriting within one fixed lexical/state scope.
//! Callers select substitutions; numeric callbacks use the existing scoped
//! term rewriter. Replacements are simultaneous and are not visited again.
use super::super::addresses::SharedAddressBase;
use super::super::offsets::{KernelAddressOffset, SharedAddressOffset};
use super::*;

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum PointerRewriteError<E> {
    Callback(E),
    IndexType,
}

pub(crate) trait PointerRewrite {
    type Error;
    fn numeric(&mut self, value: &KernelTerm) -> Result<KernelTerm, Self::Error>;
    fn address(&mut self, _value: &SharedAddress) -> Result<Option<SharedAddress>, Self::Error> {
        Ok(None)
    }
    fn block(&mut self, value: &SharedAddressBase) -> Result<SharedAddressBase, Self::Error> {
        Ok(value.clone())
    }
    fn coordinate(&mut self, variable: Variable) -> Result<SharedAddressOffset, Self::Error> {
        Ok(KernelAddressOffset::Variable(variable)
            .into_shared()
            .expect("coordinate node"))
    }
}

struct Rewrite<'a, R: PointerRewrite> {
    selected: &'a mut R,
    offsets: HashMap<SharedAddressOffset, SharedAddressOffset>,
    addresses: HashMap<SharedAddress, SharedAddress>,
    blocks: HashMap<SharedAddressBase, SharedAddressBase>,
    numeric: HashMap<KernelTerm, KernelTerm>,
}
impl<'a, R: PointerRewrite> Rewrite<'a, R> {
    fn new(selected: &'a mut R) -> Self {
        Self {
            selected,
            offsets: Default::default(),
            addresses: Default::default(),
            blocks: Default::default(),
            numeric: Default::default(),
        }
    }
    fn numeric(&mut self, value: &KernelTerm) -> Result<KernelTerm, PointerRewriteError<R::Error>> {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(result) = self.numeric.get(value) {
            return Ok(result.clone());
        }
        let result = self
            .selected
            .numeric(value)
            .map_err(PointerRewriteError::Callback)?;
        if result.ty() != value.ty() {
            return Err(PointerRewriteError::IndexType);
        }
        self.numeric.insert(value.clone(), result.clone());
        Ok(result)
    }
    fn offset(
        &mut self,
        root: &SharedAddressOffset,
    ) -> Result<SharedAddressOffset, PointerRewriteError<R::Error>> {
        let mut pending = vec![(root, false)];
        while let Some((offset, finish)) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if self.offsets.contains_key(offset) {
                continue;
            }
            let result = match offset.node() {
                KernelAddressOffset::Constant(_) => offset.clone(),
                KernelAddressOffset::Variable(variable) => self
                    .selected
                    .coordinate(*variable)
                    .map_err(PointerRewriteError::Callback)?,
                KernelAddressOffset::Add([left, right]) => {
                    if !finish {
                        pending.extend([(offset, true), (right, false), (left, false)]);
                        continue;
                    }
                    let a = self.offsets[left].clone();
                    let b = self.offsets[right].clone();
                    if &a == left && &b == right {
                        offset.clone()
                    } else {
                        KernelAddressOffset::Add([a, b])
                            .into_shared()
                            .expect("offset children")
                    }
                }
                KernelAddressOffset::Int32Scaled { value, byte_width } => {
                    let result = self.numeric(value)?;
                    if &result == value {
                        offset.clone()
                    } else {
                        KernelAddressOffset::Int32Scaled {
                            value: result,
                            byte_width: *byte_width,
                        }
                        .into_shared()
                        .map_err(|_| PointerRewriteError::IndexType)?
                    }
                }
                KernelAddressOffset::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => {
                    let result = self.numeric(value)?;
                    if &result == value {
                        offset.clone()
                    } else {
                        KernelAddressOffset::Int64Scaled {
                            value: result,
                            byte_width: *byte_width,
                            unsigned: *unsigned,
                        }
                        .into_shared()
                        .map_err(|_| PointerRewriteError::IndexType)?
                    }
                }
            };
            self.offsets.insert(offset.clone(), result);
        }
        Ok(self.offsets[root].clone())
    }
    fn address(
        &mut self,
        value: &SharedAddress,
    ) -> Result<SharedAddress, PointerRewriteError<R::Error>> {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(result) = self.addresses.get(value) {
            return Ok(result.clone());
        }
        let result = if let Some(replacement) = self
            .selected
            .address(value)
            .map_err(PointerRewriteError::Callback)?
        {
            replacement
        } else {
            let source = value.block();
            let block = if let Some(block) = self.blocks.get(&source) {
                block.clone()
            } else {
                let block = self
                    .selected
                    .block(&source)
                    .map_err(PointerRewriteError::Callback)?;
                self.blocks.insert(source, block.clone());
                block
            };
            let offset = self.offset(value.offset())?;
            if value.has_block(&block) && &offset == value.offset() {
                value.clone()
            } else {
                SharedAddress::new(block, offset)
            }
        };
        self.addresses.insert(value.clone(), result.clone());
        Ok(result)
    }
    fn pointer(
        &mut self,
        value: &SharedPointer,
    ) -> Result<SharedPointer, PointerRewriteError<R::Error>> {
        let source = value.node();
        let address = self.address(&source.address)?;
        let provenance = self.address(&source.provenance)?;
        let owner = source
            .array
            .owner()
            .map(|address| self.address(address))
            .transpose()?;
        let mut array_changed = owner.as_ref() != source.array.owner();
        let mut bounds = source.array.bounds().cloned();
        if let Some(selected) = source.array.bounds() {
            let start = self.address(&selected.start)?;
            let width = self.numeric(selected.width())?;
            if start != selected.start || width != *selected.width() {
                array_changed = true;
                bounds = Some(KernelSubobjectBounds::new(start, width));
            }
        }
        if address == source.address && provenance == source.provenance && !array_changed {
            return Ok(value.clone());
        }
        Ok(SharedPointer::new(KernelPointer {
            address,
            provenance,
            array: KernelArrayObject::from_parts(source.array.is_known(), bounds, owner),
            program_type: source.program_type,
            qualifiers: source.qualifiers.clone(),
        }))
    }
}
impl SharedPointer {
    /// Memos belong to this call's fixed scope, never to a global substitution.
    pub(crate) fn try_rewrite<R: PointerRewrite>(
        &self,
        selected: &mut R,
    ) -> Result<Self, PointerRewriteError<R::Error>> {
        Rewrite::new(selected).pointer(self)
    }
}
impl SharedAddress {
    pub(crate) fn try_rewrite<R: PointerRewrite>(
        &self,
        selected: &mut R,
    ) -> Result<Self, PointerRewriteError<R::Error>> {
        Rewrite::new(selected).address(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    struct Identity;
    impl PointerRewrite for Identity {
        type Error = ();
        fn numeric(&mut self, value: &KernelTerm) -> Result<KernelTerm, ()> {
            Ok(value.clone())
        }
    }
    #[test]
    fn unchanged_rewrite_preserves_exact_complete_payload_handle() {
        let source = super::super::tests::complete_source().into_shared();
        assert_eq!(source.try_rewrite(&mut Identity).unwrap(), source);
    }
    #[test]
    fn selected_address_replacements_are_simultaneous_and_keep_metadata() {
        let source = super::super::tests::complete_source().into_shared();
        let replacement = Address::symbolic(Variable(1004000)).shared().clone();
        struct Selected {
            from: SharedAddress,
            to: SharedAddress,
        }
        impl PointerRewrite for Selected {
            type Error = ();
            fn numeric(&mut self, value: &KernelTerm) -> Result<KernelTerm, ()> {
                Ok(value.clone())
            }
            fn address(&mut self, value: &SharedAddress) -> Result<Option<SharedAddress>, ()> {
                Ok((value == &self.from).then(|| self.to.clone()))
            }
            fn block(&mut self, block: &SharedAddressBase) -> Result<SharedAddressBase, ()> {
                assert_ne!(
                    block.native_atom(),
                    &AddressBase::Symbolic(Variable(1004000)),
                    "replacement must not be rewritten"
                );
                Ok(block.clone())
            }
        }
        let output = source
            .try_rewrite(&mut Selected {
                from: source.node().address.clone(),
                to: replacement.clone(),
            })
            .unwrap();
        assert_eq!(output.node().address, replacement);
        assert_eq!(output.node().provenance, source.node().provenance);
        assert_eq!(output.node().array.owner(), source.node().array.owner());
        assert!(Arc::ptr_eq(
            output.node().qualifiers.as_ref().unwrap(),
            source.node().qualifiers.as_ref().unwrap()
        ));
    }
    #[test]
    fn numeric_substitution_uses_existing_fold_capture_avoidance_without_export() {
        use crate::kernel::proof::term_rewrite::TermRewrite;
        let _session = crate::kernel::VerificationSession::enter();
        let free = Variable(1004010);
        let item = Variable(1004011);
        let native = OldMachineTerm::RangeFold {
            start: Box::new(OldMachineTerm::constant(0)),
            end: Box::new(OldMachineTerm::Variable(free)),
            initial: Box::new(OldMachineTerm::constant(0)),
            accumulator: Variable(1004012),
            item,
            body: Box::new(OldMachineTerm::Variable(item)),
        };
        let index = KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
        let offset = KernelAddressOffset::Int32Scaled {
            value: index,
            byte_width: -4,
        }
        .into_shared()
        .unwrap();
        let block = SharedAddressBase::new(AddressBase::Symbolic(Variable(1004013)));
        let address = SharedAddress::new(block, offset);
        struct Scoped<'a, 'b>(&'a mut TermRewrite<'b>);
        impl PointerRewrite for Scoped<'_, '_> {
            type Error = &'static str;
            fn numeric(&mut self, value: &KernelTerm) -> Result<KernelTerm, Self::Error> {
                let result = self.0.shared_machine_operand(value);
                if self.0.refusal().is_some() {
                    return Err("scoped rewrite refused");
                }
                result.ok_or("unsupported shared child")
            }
        }
        let from = OldMachineTerm::Variable(free);
        let to = OldMachineTerm::Variable(item);
        let mut scoped = TermRewrite::for_bits_checked(&from, &to);
        let exports = KernelTermExport::machine_export_count();
        let output = address.try_rewrite(&mut Scoped(&mut scoped)).unwrap();
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        let KernelAddressOffset::Int32Scaled { value, byte_width } = output.offset().node() else {
            panic!("scaled fold")
        };
        assert_eq!(*byte_width, -4);
        let KernelTermNode::Fold(fold) = value.node() else {
            panic!("retained fold")
        };
        assert_ne!(fold.item, item);
        assert!(
            matches!(fold.arguments[1].node(), KernelTermNode::Variable(variable) if *variable == item)
        );
        assert!(
            matches!(fold.arguments[3].node(), KernelTermNode::Variable(variable) if *variable == fold.item)
        );
    }
    #[test]
    fn callback_refusal_and_wrong_numeric_carrier_leave_source_unchanged() {
        let source = super::super::tests::complete_source().into_shared();
        struct Refuse(bool);
        impl PointerRewrite for Refuse {
            type Error = &'static str;
            fn numeric(&mut self, _: &KernelTerm) -> Result<KernelTerm, Self::Error> {
                if self.0 {
                    Err("selected rewrite refused")
                } else {
                    Ok(KernelTerm::integer_literal(0.into()))
                }
            }
        }
        assert_eq!(
            source.try_rewrite(&mut Refuse(true)),
            Err(PointerRewriteError::Callback("selected rewrite refused"))
        );
        assert_eq!(
            source.try_rewrite(&mut Refuse(false)),
            Err(PointerRewriteError::IndexType)
        );
        assert_eq!(
            source.node().array.bounds().unwrap().width().ty(),
            &KernelType::Program(ProgramType::Int32)
        );
    }
}
#[cfg(test)]
mod scaling_tests {
    include!("../../../../scaling_tests/kernel/primitives/kernel_term/pointers/rewrite.rs");
}
