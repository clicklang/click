//! Checked absence of future uses for a selected scalar-reference binding.
//! This is source evidence for subsequent local authority integration; it
//! neither grants memory authority nor ends a production loan.

use super::schema::{Expression as E, Function, MirStatement as S, MirTerminator as T, Type};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct MirPoint {
    pub block: usize,
    /// Number of statements already executed in this block.
    pub statement: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScalarReferenceAccessKind {
    Read,
    Write,
}

/// One memory operation through the selected reference instance. The private
/// constructor retains the exact immutable source expression and borrow
/// origin; a variable name or caller-supplied alias list is not a binding.
#[derive(Debug)]
pub struct CheckedScalarReferenceAccess<'a> {
    function: &'a Function,
    import_identity: &'a str,
    borrow: MirPoint,
    point: MirPoint,
    occurrence: usize,
    source_node: usize,
    place: &'a E,
    reference: &'a str,
    kind: ScalarReferenceAccessKind,
}

/// A source binding joined with a completed kernel memory observation.
/// This retains the execution that produced it and grants no memory authority.
#[derive(Debug)]
pub struct CheckedExecutedScalarReferenceAccess<'a, 'e> {
    access: &'a CheckedScalarReferenceAccess<'a>,
    event: crate::kernel::ExecutedReferenceAccess<'e>,
    execution: &'e crate::kernel::SymbolicCExecution,
}
impl CheckedExecutedScalarReferenceAccess<'_, '_> {
    pub fn source_access(&self) -> &CheckedScalarReferenceAccess<'_> {
        self.access
    }
    pub fn pointer(&self) -> &crate::kernel::Pointer {
        self.event.pointer()
    }
    pub fn execution(&self) -> &crate::kernel::SymbolicCExecution {
        self.execution
    }
}

impl CheckedScalarReferenceAccess<'_> {
    pub fn function(&self) -> &Function {
        self.function
    }
    pub fn import_identity(&self) -> &str {
        self.import_identity
    }
    pub fn borrow_point(&self) -> MirPoint {
        self.borrow
    }
    pub fn point(&self) -> MirPoint {
        self.point
    }
    pub fn occurrence(&self) -> usize {
        self.occurrence
    }
    pub fn place(&self) -> &E {
        self.place
    }
    pub fn reference_local(&self) -> &str {
        self.reference
    }
    pub fn kind(&self) -> ScalarReferenceAccessKind {
        self.kind
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FrontierRefusal {
    MissingMir,
    InvalidPoint,
    UnsupportedBorrow,
    UnsupportedFlow,
    ReferenceEscape,
    FutureUse,
}

/// The source is immutably borrowed for the certificate's entire lifetime.
/// No caller-supplied list of aliases or purported last uses is trusted.
#[derive(Debug)]
pub struct CheckedScalarReferenceEnd<'a> {
    function: &'a Function,
    import_identity: &'a str,
    borrow: MirPoint,
    end: MirPoint,
    accesses: BTreeMap<MirPoint, Vec<CheckedScalarReferenceAccess<'a>>>,
    access_index: BTreeMap<(MirPoint, usize), usize>,
}

impl CheckedScalarReferenceEnd<'_> {
    pub fn import_identity(&self) -> &str {
        self.import_identity
    }
    pub fn function(&self) -> &Function {
        self.function
    }
    pub fn borrow_point(&self) -> MirPoint {
        self.borrow
    }
    pub fn end_point(&self) -> MirPoint {
        self.end
    }
    /// Indexed source evidence only; absence is not a memory permission.
    pub fn memory_accesses_at(&self, point: MirPoint) -> &[CheckedScalarReferenceAccess<'_>] {
        crate::instrumentation::record_deterministic_work(1);
        self.accesses.get(&point).map(Vec::as_slice).unwrap_or(&[])
    }
    /// Bind only producer observations with the same locked source, exact
    /// operation and reference origin. A submitted name or address is not
    /// sufficient. Each lookup uses the selected certificate's index.
    pub fn bind_executed_accesses<'a, 'e>(
        &'a self,
        execution: &'e crate::kernel::SymbolicCExecution,
    ) -> Vec<CheckedExecutedScalarReferenceAccess<'a, 'e>> {
        execution
            .executed_reference_accesses()
            .filter_map(|event| {
                crate::instrumentation::record_deterministic_work(1);
                let source = event.source();
                if source.import_identity.as_ref() != self.import_identity
                    || source.function.as_ref() != self.function.name
                {
                    return None;
                }
                let point = MirPoint {
                    block: source.block,
                    statement: source.statement,
                };
                let index = *self.access_index.get(&(point, source.node))?;
                let access = &self.accesses.get(&point)?[index];
                let kind = match source.kind {
                    crate::kernel::ReferenceAccessKind::Read => ScalarReferenceAccessKind::Read,
                    crate::kernel::ReferenceAccessKind::Write => ScalarReferenceAccessKind::Write,
                };
                (access.kind == kind && source.reference_local.as_ref() == access.reference)
                    .then_some(CheckedExecutedScalarReferenceAccess {
                        access,
                        event,
                        execution,
                    })
            })
            .collect()
    }
}

// Both the checker and lowering number immutable expression nodes in this
// order. Keys are node addresses, never structural expressions or proof state.
pub(super) fn mir_expression_nodes(statement: &S) -> BTreeMap<usize, usize> {
    fn visit(expr: &E, nodes: &mut BTreeMap<usize, usize>) {
        crate::instrumentation::record_deterministic_work(1);
        nodes.insert(expr as *const E as usize, nodes.len());
        let children: Vec<&E> = match expr {
            E::Borrow { place, .. } => vec![place],
            E::Deref { reference, .. } => vec![reference],
            E::Field { base, .. } => vec![base],
            E::Index { slice, index } => vec![slice, index],
            E::IntegerFrom { value, .. }
            | E::Not { value }
            | E::BitwiseNot { value, .. }
            | E::Cast { value, .. }
            | E::Repeat { value, .. } => vec![value],
            E::SliceLength { slice } | E::ArrayToSlice { array: slice, .. } => vec![slice],
            E::Binary { left, right, .. } => vec![left, right],
            E::Call { arguments, .. }
            | E::Array {
                elements: arguments,
                ..
            } => arguments.iter().collect(),
            _ => vec![],
        };
        for child in children {
            visit(child, nodes);
        }
    }
    let mut nodes = BTreeMap::new();
    if let S::Assign { target, value } = statement {
        visit(value, &mut nodes);
        visit(target, &mut nodes);
    }
    nodes
}

fn direct_alias_source(expr: &E) -> Option<&str> {
    match expr {
        E::Local { name } => Some(name),
        E::Borrow { place, .. } => match place.as_ref() {
            E::Deref { reference, .. } => match reference.as_ref() {
                E::Local { name } => Some(name),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

struct AccessCollector<'a, 'b> {
    function: &'a Function,
    import_identity: &'a str,
    borrow: MirPoint,
    point: MirPoint,
    types: &'b BTreeMap<&'a str, &'a Type>,
    aliases: &'b BTreeSet<&'a str>,
    nodes: &'b BTreeMap<usize, usize>,
    accesses: Vec<CheckedScalarReferenceAccess<'a>>,
}

impl<'a> AccessCollector<'a, '_> {
    // Address computation does not read the addressed scalar. Operands used
    // to compute an address (e.g. an index) still perform their normal reads.
    fn expression(
        &mut self,
        expr: &'a E,
        kind: Option<ScalarReferenceAccessKind>,
    ) -> Result<bool, FrontierRefusal> {
        use ScalarReferenceAccessKind::Read;
        crate::instrumentation::record_deterministic_work(1);
        let children: Vec<(&E, Option<ScalarReferenceAccessKind>)> = match expr {
            E::Local { name } => return Ok(self.aliases.contains(name.as_str())),
            E::Borrow { place, .. } => return self.expression(place, None),
            E::Deref {
                reference,
                value_type,
            } => {
                let selected = matches!(reference.as_ref(), E::Local { name } if self.aliases.contains(name.as_str()));
                if selected {
                    let E::Local { name } = reference.as_ref() else {
                        unreachable!()
                    };
                    if !matches!(self.types.get(name.as_str()), Some(Type::Reference { pointee, .. }) if pointee.as_ref() == value_type)
                    {
                        return Err(FrontierRefusal::UnsupportedFlow);
                    }
                    if kind == Some(ScalarReferenceAccessKind::Write)
                        && !matches!(
                            self.types.get(name.as_str()),
                            Some(Type::Reference { mutable: true, .. })
                        )
                    {
                        return Err(FrontierRefusal::UnsupportedFlow);
                    }
                    if let Some(kind) = kind {
                        self.accesses.push(CheckedScalarReferenceAccess {
                            function: self.function,
                            import_identity: self.import_identity,
                            borrow: self.borrow,
                            point: self.point,
                            occurrence: self.accesses.len(),
                            source_node: self.nodes[&(expr as *const E as usize)],
                            place: expr,
                            reference: name,
                            kind,
                        });
                    }
                }
                let used = self.expression(reference, Some(Read))?;
                if used && !selected {
                    return Err(FrontierRefusal::ReferenceEscape);
                }
                return Ok(used);
            }
            E::Field { base, .. } => vec![(base, None)],
            E::Index { slice, index } => vec![(slice, Some(Read)), (index, Some(Read))],
            E::ArrayToSlice { array, .. } => vec![(array, None)],
            E::SliceLength { slice } => vec![(slice, Some(Read))],
            E::IntegerFrom { value, .. }
            | E::Not { value }
            | E::BitwiseNot { value, .. }
            | E::Cast { value, .. }
            | E::Repeat { value, .. } => vec![(value, Some(Read))],
            E::Binary { left, right, .. } => vec![(left, Some(Read)), (right, Some(Read))],
            E::Call { arguments, .. }
            | E::Array {
                elements: arguments,
                ..
            } => arguments.iter().map(|arg| (arg, Some(Read))).collect(),
            E::FunctionAddress { .. }
            | E::Integer { .. }
            | E::UnsignedInteger { .. }
            | E::UsizeInteger { .. }
            | E::Boolean { .. } => return Ok(false),
            _ => return Err(FrontierRefusal::UnsupportedFlow),
        };
        let mut used = false;
        for (child, kind) in children {
            used |= self.expression(child, kind)?;
        }
        Ok(used)
    }
}

fn scalar_reference(ty: &Type) -> bool {
    matches!(ty, Type::Reference { pointee, .. }
        if matches!(pointee.as_ref(), Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Bool))
}

fn scalar_value(expr: &E, types: &BTreeMap<&str, &Type>) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    let scalar = |ty: &Type| {
        matches!(
            ty,
            Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Bool
        )
    };
    match expr {
        E::Integer { .. } | E::UnsignedInteger { .. } | E::Boolean { .. } => true,
        E::Local { name } => types.get(name.as_str()).is_some_and(|ty| scalar(ty)),
        E::Deref { value_type, .. } => scalar(value_type),
        E::Not { value } | E::BitwiseNot { value, .. } => scalar_value(value, types),
        E::Cast { value, value_type } => scalar(value_type) && scalar_value(value, types),
        E::Binary {
            left,
            right,
            left_type,
            right_type,
            ..
        } => {
            scalar(left_type)
                && scalar(right_type)
                && scalar_value(left, types)
                && scalar_value(right, types)
        }
        _ => false,
    }
}

// Each operand is visited once. The second bit detects opaque alias capture,
// including calls/aggregates nested inside otherwise scalar expressions.
fn alias_effect(expr: &E, aliases: &BTreeSet<&str>) -> Result<(bool, bool), FrontierRefusal> {
    crate::instrumentation::record_deterministic_work(1);
    let children: Vec<&E> = match expr {
        E::Local { name } => return Ok((aliases.contains(name.as_str()), false)),
        E::IntegerFrom { value, .. }
        | E::Not { value }
        | E::BitwiseNot { value, .. }
        | E::Cast { value, .. }
        | E::Repeat { value, .. } => vec![value],
        E::Borrow { place, .. } => vec![place],
        E::Deref { reference, .. } => vec![reference],
        E::Field { base, .. } => vec![base],
        E::SliceLength { slice } | E::ArrayToSlice { array: slice, .. } => vec![slice],
        E::Index { slice, index } => vec![slice, index],
        E::Binary { left, right, .. } => vec![left, right],
        E::Call { arguments, .. }
        | E::Array {
            elements: arguments,
            ..
        } => arguments.iter().collect(),
        E::FunctionAddress { .. }
        | E::Integer { .. }
        | E::UnsignedInteger { .. }
        | E::UsizeInteger { .. }
        | E::Boolean { .. } => return Ok((false, false)),
        E::SharedArrayHasNext { .. }
        | E::SharedArrayOptionElement { .. }
        | E::SharedArrayOptionTag { .. }
        | E::ChunkHasNext { .. }
        | E::ChunkOptionSlice { .. }
        | E::ChunkOptionTag { .. }
        | E::ChunkRemainder { .. } => return Err(FrontierRefusal::UnsupportedFlow),
    };
    let mut used = false;
    let mut escaped = false;
    for child in children {
        let (child_used, child_escaped) = alias_effect(child, aliases)?;
        used |= child_used;
        escaped |= child_escaped;
    }
    // Conversion of a selected reference into a scalar must not hide its
    // identity. Conservatively refuse conversions even of loaded values;
    // distinguishing pointer transport from scalar reads is later coverage.
    escaped |= used
        && matches!(
            expr,
            E::Call { .. }
                | E::Array { .. }
                | E::Repeat { .. }
                | E::Cast { .. }
                | E::IntegerFrom { .. }
        );
    Ok((used, escaped))
}

fn transfer<'a>(
    statement: &'a S,
    types: &BTreeMap<&str, &Type>,
    aliases: &mut BTreeSet<&'a str>,
    after_end: bool,
) -> Result<(), FrontierRefusal> {
    crate::instrumentation::record_deterministic_work(1);
    match statement {
        S::Assign { target, value } => {
            let (source_uses, source_escapes) = alias_effect(value, aliases)?;
            if source_escapes {
                return Err(FrontierRefusal::ReferenceEscape);
            }
            let (target_uses, target_escapes) = if matches!(target, E::Local { .. }) {
                (false, false)
            } else {
                alias_effect(target, aliases)?
            };
            if target_escapes {
                return Err(FrontierRefusal::ReferenceEscape);
            }
            if after_end && (source_uses || target_uses) {
                return Err(FrontierRefusal::FutureUse);
            }
            if let E::Local { name } = target {
                let ty = types
                    .get(name.as_str())
                    .ok_or(FrontierRefusal::UnsupportedFlow)?;
                if scalar_reference(ty) {
                    if source_uses {
                        // A scalar read used to choose another address does
                        // not make that address an alias of this borrow.
                        let source = direct_alias_source(value)
                            .filter(|source| aliases.contains(*source))
                            .ok_or(FrontierRefusal::UnsupportedFlow)?;
                        if !matches!((types.get(source), ty),
                            (Some(Type::Reference { pointee: source, mutable: source_mutable }), Type::Reference { pointee: target, mutable: target_mutable }) if source == target && (!target_mutable || *source_mutable))
                        {
                            return Err(FrontierRefusal::UnsupportedFlow);
                        }
                        aliases.insert(name);
                    } else {
                        aliases.remove(name.as_str());
                    }
                } else if source_uses
                    && (!matches!(
                        ty,
                        Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Bool
                    ) || !scalar_value(value, types))
                {
                    // Do not lose an alias inside a record, array, cast or call.
                    return Err(FrontierRefusal::ReferenceEscape);
                }
            } else if source_uses && !scalar_value(value, types) {
                return Err(FrontierRefusal::ReferenceEscape);
            }
            Ok(())
        }
        S::BeginStorage { .. } | S::EndStorage { .. } => {
            // Storage events alone prove no loan ending. Retain aliases until
            // an actual definition replaces them, even across StorageDead.
            Ok(())
        }
        // Aggregate and iterator alias transport needs separate evidence.
        _ => Err(FrontierRefusal::UnsupportedFlow),
    }
}

/// Certify a same-block borrow/frontier and its acyclic straight-line
/// continuation. Branches, loops and aggregate transport are refused rather
/// than assigning them guessed lifetimes. Reference copies/reborrows and
/// replacement definitions are followed from the selected borrow itself.
pub(super) fn certify_scalar_reference_end<'a>(
    function: &'a Function,
    import_identity: &'a str,
    borrow: MirPoint,
    end: MirPoint,
) -> Result<CheckedScalarReferenceEnd<'a>, FrontierRefusal> {
    if !matches!(
        function.return_type,
        Type::Unit | Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Bool
    ) {
        return Err(FrontierRefusal::UnsupportedFlow);
    }
    let mir = function.mir.as_ref().ok_or(FrontierRefusal::MissingMir)?;
    let block = mir
        .blocks
        .get(borrow.block)
        .ok_or(FrontierRefusal::InvalidPoint)?;
    if end.block != borrow.block
        || end.statement <= borrow.statement
        || end.statement > block.statements.len()
    {
        return Err(FrontierRefusal::InvalidPoint);
    }
    let mut types = BTreeMap::new();
    for local in function.parameters.iter().chain(&mir.locals) {
        crate::instrumentation::record_deterministic_work(1);
        if types
            .insert(local.name.as_str(), &local.value_type)
            .is_some()
        {
            return Err(FrontierRefusal::UnsupportedFlow);
        }
    }
    let Some(S::Assign {
        target: E::Local { name },
        value: E::Borrow { place, value_type },
    }) = block.statements.get(borrow.statement)
    else {
        return Err(FrontierRefusal::UnsupportedBorrow);
    };
    if !matches!(value_type, Type::Reference { mutable: true, .. })
        || !scalar_reference(value_type)
        || types.get(name.as_str()).copied() != Some(value_type)
    {
        return Err(FrontierRefusal::UnsupportedBorrow);
    }
    let E::Deref {
        reference,
        value_type: pointee,
    } = place.as_ref()
    else {
        return Err(FrontierRefusal::UnsupportedBorrow);
    };
    let E::Local { name: parent } = reference.as_ref() else {
        return Err(FrontierRefusal::UnsupportedBorrow);
    };
    if !matches!(types.get(parent.as_str()), Some(Type::Reference { mutable: true, pointee: parent_ty })
        if parent_ty.as_ref() == pointee)
        || !matches!(value_type, Type::Reference { pointee: child_ty, .. } if child_ty.as_ref() == pointee)
    {
        return Err(FrontierRefusal::UnsupportedBorrow);
    }
    let mut aliases = BTreeSet::from([name.as_str()]);
    let mut accesses = BTreeMap::new();
    let mut access_index = BTreeMap::new();
    for (offset, statement) in block.statements[borrow.statement + 1..end.statement]
        .iter()
        .enumerate()
    {
        let point = MirPoint {
            block: borrow.block,
            statement: borrow.statement + 1 + offset,
        };
        let nodes = mir_expression_nodes(statement);
        let mut collector = AccessCollector {
            function,
            import_identity,
            borrow,
            point,
            types: &types,
            aliases: &aliases,
            nodes: &nodes,
            accesses: vec![],
        };
        if let S::Assign { target, value } = statement {
            collector.expression(value, Some(ScalarReferenceAccessKind::Read))?;
            collector.expression(target, Some(ScalarReferenceAccessKind::Write))?;
        }
        if !collector.accesses.is_empty() {
            for (index, access) in collector.accesses.iter().enumerate() {
                access_index.insert((point, access.source_node), index);
            }
            accesses.insert(point, collector.accesses);
        }
        transfer(statement, &types, &mut aliases, false)?;
    }
    let mut point = end;
    let mut visited = BTreeSet::new();
    loop {
        if !visited.insert(point.block) {
            return Err(FrontierRefusal::UnsupportedFlow);
        }
        let block = mir
            .blocks
            .get(point.block)
            .ok_or(FrontierRefusal::InvalidPoint)?;
        for statement in &block.statements[point.statement..] {
            transfer(statement, &types, &mut aliases, true)?;
        }
        match &block.terminator {
            T::Return | T::Unreachable => break,
            T::Goto { target } => {
                point = MirPoint {
                    block: *target,
                    statement: 0,
                }
            }
            T::Call {
                arguments,
                owned_arguments,
                destination,
                target,
                function,
                through_pointer,
            } => {
                let mut used = *through_pointer && aliases.contains(function.as_str());
                used |= owned_arguments
                    .iter()
                    .any(|arg| aliases.contains(arg.local.as_str()));
                for argument in arguments {
                    used |= alias_effect(argument, &aliases)?.0;
                }
                if used {
                    return Err(FrontierRefusal::FutureUse);
                }
                // A call whose inputs contain no selected alias cannot carry
                // that alias into its result; earlier aggregate escapes were refused.
                aliases.remove(destination.as_str());
                point = MirPoint {
                    block: *target,
                    statement: 0,
                };
            }
            T::If { .. } | T::Drop { .. } => return Err(FrontierRefusal::UnsupportedFlow),
        }
    }
    Ok(CheckedScalarReferenceEnd {
        function,
        import_identity,
        borrow,
        end,
        accesses,
        access_index,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::rust::schema::{MirBlock, MirBody, Place, Span};

    fn local(name: &str) -> E {
        E::Local { name: name.into() }
    }
    fn reference_type() -> Type {
        Type::Reference {
            mutable: true,
            pointee: Box::new(Type::I32),
        }
    }
    fn deref(name: &str) -> E {
        E::Deref {
            reference: Box::new(local(name)),
            value_type: Type::I32,
        }
    }
    fn borrow_parent() -> E {
        E::Borrow {
            place: Box::new(deref("parent")),
            value_type: reference_type(),
        }
    }
    fn assign(target: E, value: E) -> S {
        S::Assign { target, value }
    }
    fn place(name: &str, value_type: Type) -> Place {
        Place {
            name: name.into(),
            value_type,
            span: Span { line: 1, column: 1 },
        }
    }
    fn function() -> Function {
        Function {
            name: "test::reuse".into(),
            return_type: Type::Unit,
            parameters: vec![
                place("parent", reference_type()),
                place("other", reference_type()),
            ],
            body: vec![],
            external: false,
            span: Span { line: 1, column: 1 },
            mir: Some(MirBody {
                locals: vec![
                    place("child", reference_type()),
                    place("alias", reference_type()),
                    place("x", Type::I32),
                ],
                blocks: vec![MirBlock {
                    statements: vec![
                        assign(local("child"), borrow_parent()),
                        assign(deref("child"), E::Integer { value: 7 }),
                        assign(deref("parent"), E::Integer { value: 8 }),
                    ],
                    terminator: T::Return,
                }],
            }),
        }
    }
    fn point(statement: usize) -> MirPoint {
        MirPoint {
            block: 0,
            statement,
        }
    }
    fn refusal(f: &Function, end: usize) -> FrontierRefusal {
        certify_scalar_reference_end(f, "test-source", point(0), point(end)).unwrap_err()
    }

    #[test]
    fn scalar_reference_frontier_covers_parent_reuse_and_rejects_early_end() {
        let f = function();
        let certificate =
            certify_scalar_reference_end(&f, "test-source", point(0), point(2)).unwrap();
        assert!(std::ptr::eq(certificate.function(), &f));
        assert_eq!(certificate.borrow_point(), point(0));
        assert_eq!(certificate.end_point(), point(2));
        assert_eq!(refusal(&f, 1), FrontierRefusal::FutureUse);
    }

    #[test]
    fn scalar_reference_frontier_follows_copies_and_does_not_trust_storage_death() {
        let mut f = function();
        let block = &mut f.mir.as_mut().unwrap().blocks[0];
        block
            .statements
            .insert(1, assign(local("alias"), local("child")));
        block.statements.insert(
            3,
            S::EndStorage {
                local: "child".into(),
            },
        );
        block
            .statements
            .push(assign(deref("alias"), E::Integer { value: 9 }));
        assert_eq!(refusal(&f, 3), FrontierRefusal::FutureUse);
        block_mut(&mut f).statements[5] = assign(deref("child"), E::Integer { value: 9 });
        assert_eq!(refusal(&f, 3), FrontierRefusal::FutureUse);
    }

    fn block_mut(f: &mut Function) -> &mut MirBlock {
        &mut f.mir.as_mut().unwrap().blocks[0]
    }

    #[test]
    fn scalar_reference_frontier_distinguishes_replacement_and_parent_reassignment() {
        let mut f = function();
        block_mut(&mut f)
            .statements
            .push(assign(local("child"), borrow_parent()));
        block_mut(&mut f)
            .statements
            .push(assign(deref("child"), E::Integer { value: 9 }));
        certify_scalar_reference_end(&f, "test-source", point(0), point(2)).unwrap();
        let mut f = function();
        block_mut(&mut f)
            .statements
            .insert(2, assign(local("parent"), local("other")));
        block_mut(&mut f)
            .statements
            .push(assign(deref("child"), E::Integer { value: 9 }));
        assert_eq!(refusal(&f, 2), FrontierRefusal::FutureUse);
    }

    #[test]
    fn scalar_reference_frontier_refuses_nested_capture_and_unchecked_paths() {
        let mut f = function();
        block_mut(&mut f).statements.insert(
            1,
            assign(
                local("x"),
                E::Binary {
                    operator: "add".into(),
                    left_type: Type::I32,
                    right_type: Type::I32,
                    left: Box::new(E::Call {
                        function: "capture".into(),
                        arguments: vec![local("child")],
                    }),
                    right: Box::new(E::Integer { value: 1 }),
                },
            ),
        );
        assert_eq!(refusal(&f, 3), FrontierRefusal::ReferenceEscape);
        block_mut(&mut f).statements[1] = assign(
            E::Deref {
                reference: Box::new(E::Call {
                    function: "capture".into(),
                    arguments: vec![local("child")],
                }),
                value_type: Type::I32,
            },
            E::Integer { value: 7 },
        );
        assert_eq!(refusal(&f, 3), FrontierRefusal::ReferenceEscape);
        block_mut(&mut f).statements[1] = assign(
            local("x"),
            E::Cast {
                value: Box::new(local("child")),
                value_type: Type::I32,
            },
        );
        assert_eq!(refusal(&f, 3), FrontierRefusal::ReferenceEscape);
        let mut f = function();
        block_mut(&mut f).terminator = T::If {
            condition: E::Boolean { value: true },
            then_target: 0,
            else_target: 0,
        };
        assert_eq!(refusal(&f, 2), FrontierRefusal::UnsupportedFlow);
        block_mut(&mut f).terminator = T::Goto { target: 0 };
        assert_eq!(refusal(&f, 2), FrontierRefusal::UnsupportedFlow);
        block_mut(&mut f).terminator = T::Goto { target: 99 };
        assert_eq!(refusal(&f, 2), FrontierRefusal::InvalidPoint);
        f.return_type = reference_type();
        assert_eq!(refusal(&f, 2), FrontierRefusal::UnsupportedFlow);
    }

    #[test]
    fn scalar_reference_frontier_selected_alias_chain_scales_linearly() {
        let mut samples = Vec::new();
        for size in [16, 64, 256, 1024] {
            let mut f = function();
            let mir = f.mir.as_mut().unwrap();
            let mut previous = "child".to_string();
            for index in 0..size {
                let name = format!("alias_{index}");
                mir.locals.push(place(&name, reference_type()));
                mir.blocks[0]
                    .statements
                    .insert(index + 1, assign(local(&name), local(&previous)));
                previous = name;
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                certify_scalar_reference_end(&f, "test-source", point(0), point(size + 2)).unwrap()
            });
            samples.push((size, work));
            assert!(
                work <= size * 9 + 64,
                "alias chain revisited prefixes: {samples:?}"
            );
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1 * 4 + 48,
                "superlinear alias checking: {samples:?}"
            );
        }
    }

    #[test]
    fn scalar_reference_frontier_checks_call_continuations_and_points() {
        let mut f = function();
        block_mut(&mut f).terminator = T::Call {
            function: "observe_parent".into(),
            arguments: vec![local("parent")],
            owned_arguments: vec![],
            destination: "x".into(),
            target: 1,
            through_pointer: false,
        };
        f.mir.as_mut().unwrap().blocks.push(MirBlock {
            statements: vec![],
            terminator: T::Return,
        });
        certify_scalar_reference_end(&f, "test-source", point(0), point(2)).unwrap();
        if let T::Call { arguments, .. } = &mut block_mut(&mut f).terminator {
            *arguments = vec![local("child")];
        }
        assert_eq!(refusal(&f, 2), FrontierRefusal::FutureUse);
        assert_eq!(refusal(&f, 99), FrontierRefusal::InvalidPoint);
        assert_eq!(
            certify_scalar_reference_end(
                &f,
                "test-source",
                MirPoint {
                    block: 99,
                    statement: 0
                },
                point(2)
            )
            .unwrap_err(),
            FrontierRefusal::InvalidPoint
        );
    }

    #[test]
    fn scalar_reference_accesses_bind_reads_writes_and_exact_source_occurrences() {
        let mut f = function();
        block_mut(&mut f).statements.insert(
            1,
            assign(
                local("alias"),
                E::Borrow {
                    place: Box::new(deref("child")),
                    value_type: reference_type(),
                },
            ),
        );
        block_mut(&mut f)
            .statements
            .insert(2, assign(deref("alias"), deref("child")));
        let certificate =
            certify_scalar_reference_end(&f, "locked-source", point(0), point(4)).unwrap();
        assert!(
            certificate.memory_accesses_at(point(1)).is_empty(),
            "reborrowing computes an address, not a scalar load"
        );
        let accesses = certificate.memory_accesses_at(point(2));
        assert_eq!(accesses.len(), 2);
        let S::Assign { target, value } = &f.mir.as_ref().unwrap().blocks[0].statements[2] else {
            panic!()
        };
        for (access, kind, name, expression, occurrence) in [
            (
                &accesses[0],
                ScalarReferenceAccessKind::Read,
                "child",
                value,
                0,
            ),
            (
                &accesses[1],
                ScalarReferenceAccessKind::Write,
                "alias",
                target,
                1,
            ),
        ] {
            assert_eq!(access.kind(), kind);
            assert_eq!(access.reference_local(), name);
            assert_eq!(access.point(), point(2));
            assert_eq!(access.occurrence(), occurrence);
            assert_eq!(access.borrow_point(), point(0));
            assert_eq!(access.import_identity(), "locked-source");
            assert!(std::ptr::eq(access.function(), &f));
            assert!(std::ptr::eq(access.place(), expression));
        }
        assert_eq!(certificate.memory_accesses_at(point(3)).len(), 1);
        assert!(
            certificate.memory_accesses_at(point(4)).is_empty(),
            "parent access is not a child access"
        );
        assert!(certificate.memory_accesses_at(point(99)).is_empty());
    }

    #[test]
    fn scalar_reference_accesses_keep_copies_bound_after_child_replacement() {
        let mut f = function();
        block_mut(&mut f).statements = vec![
            assign(local("child"), borrow_parent()),
            assign(local("alias"), local("child")),
            assign(
                local("child"),
                E::Borrow {
                    place: Box::new(deref("other")),
                    value_type: reference_type(),
                },
            ),
            assign(deref("child"), E::Integer { value: 3 }),
            assign(deref("alias"), E::Integer { value: 7 }),
        ];
        let first = certify_scalar_reference_end(&f, "source", point(0), point(5)).unwrap();
        let second = certify_scalar_reference_end(&f, "source", point(2), point(5)).unwrap();
        assert!(first.memory_accesses_at(point(3)).is_empty());
        assert_eq!(
            first.memory_accesses_at(point(4))[0].reference_local(),
            "alias"
        );
        assert_eq!(
            second.memory_accesses_at(point(3))[0].reference_local(),
            "child"
        );
        assert!(second.memory_accesses_at(point(4)).is_empty());
        assert_ne!(first.borrow_point(), second.borrow_point());
        assert_eq!(refusal(&f, 3), FrontierRefusal::FutureUse);
    }

    #[test]
    fn scalar_reference_accesses_refuse_value_dependency_as_pointer_identity() {
        let mut f = function();
        // The child value chooses another place. That reference does not
        // designate the selected borrowed scalar merely because it uses it.
        block_mut(&mut f).statements.insert(
            1,
            assign(
                local("alias"),
                E::Borrow {
                    place: Box::new(E::Index {
                        slice: Box::new(local("other")),
                        index: Box::new(deref("child")),
                    }),
                    value_type: reference_type(),
                },
            ),
        );
        assert_eq!(refusal(&f, 3), FrontierRefusal::UnsupportedFlow);
    }

    #[test]
    fn scalar_reference_accesses_index_and_lookup_scale_with_selected_operations() {
        let mut samples = Vec::new();
        for size in [16, 64, 256, 1024] {
            let mut f = function();
            block_mut(&mut f).statements = vec![assign(local("child"), borrow_parent())];
            for _ in 0..size {
                block_mut(&mut f)
                    .statements
                    .push(assign(deref("child"), E::Integer { value: 7 }));
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let certificate =
                    certify_scalar_reference_end(&f, "source", point(0), point(size + 1)).unwrap();
                for index in 1..=size {
                    let accesses = certificate.memory_accesses_at(point(index));
                    assert_eq!(accesses.len(), 1);
                    assert_eq!(accesses[0].point(), point(index));
                    assert_eq!(accesses[0].kind(), ScalarReferenceAccessKind::Write);
                }
            });
            samples.push(work);
            assert!(
                work <= size * 14 + 64,
                "access indexing revisited prefixes: {samples:?}"
            );
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0] * 4 + 48,
                "superlinear access indexing: {samples:?}"
            );
        }
    }

    #[test]
    fn scalar_reference_accesses_allow_shared_reads_and_refuse_shared_writes() {
        let mut f = function();
        let shared = Type::Reference {
            mutable: false,
            pointee: Box::new(Type::I32),
        };
        f.mir.as_mut().unwrap().locals[1].value_type = shared.clone();
        block_mut(&mut f).statements = vec![
            assign(local("child"), borrow_parent()),
            assign(
                local("alias"),
                E::Borrow {
                    place: Box::new(deref("child")),
                    value_type: shared,
                },
            ),
            assign(local("x"), deref("alias")),
        ];
        let certificate = certify_scalar_reference_end(&f, "source", point(0), point(3)).unwrap();
        assert_eq!(
            certificate.memory_accesses_at(point(2))[0].kind(),
            ScalarReferenceAccessKind::Read
        );
        block_mut(&mut f).statements[2] = assign(deref("alias"), E::Integer { value: 7 });
        assert_eq!(refusal(&f, 3), FrontierRefusal::UnsupportedFlow);
        // A shared alias cannot produce a new mutable child binding either.
        block_mut(&mut f).statements[2] = assign(
            local("child"),
            E::Borrow {
                place: Box::new(deref("alias")),
                value_type: reference_type(),
            },
        );
        assert_eq!(refusal(&f, 3), FrontierRefusal::UnsupportedFlow);
    }

    fn export(f: Function) -> super::super::schema::RustExport {
        super::super::schema::RustExport {
            schema: super::super::schema::SCHEMA,
            compiler_commit: "test".into(),
            target: super::super::schema::TARGET.into(),
            edition: "2021".into(),
            overflow_checks: true,
            panic: "abort".into(),
            mir_opt_level: 0,
            logical_source: "borrow.rs".into(),
            records: vec![],
            functions: vec![f],
        }
    }

    fn execute_export(
        export: &super::super::schema::RustExport,
        identity: &str,
        owned: bool,
    ) -> crate::kernel::SymbolicCExecution {
        use crate::kernel::*;
        let (functions, _) =
            super::super::lowering::lower_with_identity(export, Some(identity)).unwrap();
        let pointer = Pointer {
            block: "executed-child".into(),
            offset: crate::kernel::PointerOffsetTerm::Constant(0),
        };
        let memory = CMemory::new()
            .with_block(pointer.block.clone(), if owned { 4 } else { 0 })
            .store(pointer.clone(), int32(4));
        let state = CState::new()
            .with_memory(memory)
            .with_local(
                "parent",
                CValue::typed_pointer(pointer.clone(), CType::Int32Pointer),
            )
            .with_local(
                "other",
                CValue::typed_pointer(pointer.clone(), CType::Int32Pointer),
            );
        let state = if owned {
            state.with_resource_context(ResourceContext::new().unchecked_with_fact(
                CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                    pointer,
                    0.into(),
                    1.into(),
                    4,
                )),
            ))
        } else {
            state
        };
        prove_symbolic_c_execution_paths(
            state,
            functions[0].to_kernel_function().body().clone(),
            PureFactContext::new(),
        )
    }

    #[test]
    fn scalar_reference_execution_binds_real_read_and_write_producers() {
        let mut f = function();
        block_mut(&mut f).statements[1] = assign(deref("child"), deref("child"));
        let export = export(f);
        let certificate =
            certify_scalar_reference_end(&export.functions[0], "locked", point(0), point(2))
                .unwrap();
        let execution = execute_export(&export, "locked", true);
        assert!(execution.limit().is_none());
        assert_eq!(execution.paths().len(), 1);
        let bindings = certificate.bind_executed_accesses(&execution);
        assert_eq!(bindings.len(), 2, "{execution:?}");
        let mut kinds: Vec<_> = bindings
            .iter()
            .map(|binding| binding.source_access().kind())
            .collect();
        kinds.sort_by_key(|kind| matches!(kind, ScalarReferenceAccessKind::Write));
        assert_eq!(
            kinds,
            vec![
                ScalarReferenceAccessKind::Read,
                ScalarReferenceAccessKind::Write
            ]
        );
        for binding in bindings {
            assert_eq!(
                binding.pointer(),
                &crate::kernel::Pointer {
                    block: "executed-child".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(0)
                }
            );
            assert!(std::ptr::eq(binding.execution(), &execution));
            assert_eq!(binding.source_access().borrow_point(), point(0));
        }
        // Same source names and pointer do not bind a different locked import.
        let other = execute_export(&export, "other-lock", true);
        assert!(certificate.bind_executed_accesses(&other).is_empty());
    }

    #[test]
    fn scalar_reference_execution_does_not_create_a_store_observation_on_failed_write() {
        let export = export(function());
        let certificate =
            certify_scalar_reference_end(&export.functions[0], "locked", point(0), point(2))
                .unwrap();
        let execution = execute_export(&export, "locked", false);
        assert!(execution.limit().is_none());
        assert_eq!(execution.paths().len(), 1);
        assert!(
            certificate.bind_executed_accesses(&execution).is_empty(),
            "{execution:?}"
        );
    }

    #[test]
    fn scalar_reference_execution_keeps_two_cached_reads_in_one_statement_distinct() {
        let mut f = function();
        block_mut(&mut f).statements[1] = assign(
            deref("child"),
            E::Binary {
                operator: "add".into(),
                left_type: Type::I32,
                right_type: Type::I32,
                left: Box::new(deref("child")),
                right: Box::new(deref("child")),
            },
        );
        let export = export(f);
        let certificate =
            certify_scalar_reference_end(&export.functions[0], "locked", point(0), point(2))
                .unwrap();
        let execution = execute_export(&export, "locked", true);
        let bindings = certificate.bind_executed_accesses(&execution);
        assert_eq!(bindings.len(), 3, "{execution:?}");
        let mut occurrences: Vec<_> = bindings
            .iter()
            .map(|binding| binding.source_access().occurrence())
            .collect();
        occurrences.sort();
        assert_eq!(occurrences, vec![0, 1, 2]);
    }
}
