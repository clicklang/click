//! Tag arithmetic on pointer addresses.
//!
//! A word of the form `address(p) + t` is a tagged address. Addition and
//! subtraction keep that form by exact modular integer identities, so no
//! obligation is needed to track it. A bit operation relies on the low
//! address bits being zero: clearing tag bits with `& ~m` keeps the address
//! with a masked tag, reading them with `& m` yields the masked tag alone,
//! and setting them with `| b` folds into the tag. Each such step is valid
//! only when the pointer is aligned to the alignment the mask presumes and
//! the tag stays below it, so a tag can never carry into or read an address
//! bit. Evaluation never rewrites a word; the decision layer applies these
//! rules when their conditions are decided, and the cast back to a pointer
//! records the undecided ones as obligations.
//!
//! Every decision here also reports the exact facts it used, so a smart
//! closure can retain them and a simple `arithmetic using` step can check
//! the same decision from those facts alone.

use super::operators::CBitwiseOperation;
use super::*;
use crate::kernel::MachineTerm;
use crate::kernel::{CompareRelation, MachineIntegerType, MachineOperandView};

pub(in crate::kernel) struct TaggedAddress {
    pub(in crate::kernel) pointer: Pointer,
    pub(in crate::kernel) tag: MachineTerm,
    pub(in crate::kernel) object_class: Option<crate::kernel::effective_type::CAccessClass>,
}

/// The exact facts a decision consulted, and whether every step could name
/// its fact. An incomplete record still decides; it just cannot certify.
pub(in crate::kernel) struct UsedFacts {
    pub(in crate::kernel) premises: Vec<Proposition>,
    pub(in crate::kernel) complete: bool,
    /// Nesting of citing decisions in progress; a decision that re-enters
    /// itself through a tag relation stops here instead of recursing.
    pub(in crate::kernel) depth: u32,
    /// Leaves ask only the fast decisions (`fast_leaf_decision`), never the
    /// general decision: the difference graph's fast path uses these rules.
    pub(in crate::kernel) fast_only: bool,
}

/// How deep citing decisions may nest before falling back to the general
/// decider; a tagged word needs at most a few levels.
const MAX_CITING_DEPTH: u32 = 6;

impl Default for UsedFacts {
    fn default() -> Self {
        Self::new()
    }
}

impl UsedFacts {
    pub(in crate::kernel) fn new() -> Self {
        Self {
            premises: Vec::new(),
            complete: true,
            depth: 0,
            fast_only: false,
        }
    }

    /// A record whose leaves never ask the general decision.
    pub(in crate::kernel) fn fast_only() -> Self {
        Self {
            fast_only: true,
            ..Self::new()
        }
    }

    fn cite(&mut self, premise: Proposition) {
        if !self.premises.contains(&premise) {
            self.premises.push(premise);
        }
    }
}

/// How an undecided alignment or tag-bound condition is treated.
enum Undecided<'a> {
    /// Leave the word unrecognized.
    Reject,
    /// Record the condition as an obligation and continue.
    Oblige(&'a mut Vec<ProofObligation>),
}

/// A refuted condition names what the operation needed.
pub(in crate::kernel) struct Refuted(pub(in crate::kernel) String);

/// A tag sum with a zero side is the other side, so a tag read from a fact
/// such as `word == address(next) + color` is exactly `color`.
fn add_tag(left: MachineTerm, right: MachineTerm) -> MachineTerm {
    if left.uint64_as_const() == Some(0) {
        return right;
    }
    if right.uint64_as_const() == Some(0) {
        return left;
    }
    MachineTerm::uint64_add(left, right)
}

/// The alignment a tag-clearing mask presumes: `!mask + 1` when the mask
/// clears exactly the low bits.
fn clearing_mask_alignment(mask: u64) -> Option<u64> {
    let alignment = (!mask).checked_add(1)?;
    alignment.is_power_of_two().then_some(alignment)
}

/// The alignment a tag-reading mask presumes: `mask + 1` when the mask
/// selects exactly the low bits.
fn reading_mask_alignment(mask: u64) -> Option<u64> {
    let alignment = mask.checked_add(1)?;
    (alignment.is_power_of_two() && alignment > 1).then_some(alignment)
}

impl PureFactContext {
    /// Decides `condition` and cites the exact fact that settled it when one
    /// can be named: a stored fact in either orientation, an alignment base
    /// fact, or nothing for a constant or a structural pointer decision. Any
    /// other route leaves the record incomplete.
    pub(in crate::kernel) fn decide_citing(
        &self,
        condition: &ConditionTerm,
        used: &mut UsedFacts,
    ) -> Option<bool> {
        if let ConditionTerm::Constant(value) = condition {
            return Some(*value);
        }
        for stored in [condition.clone(), condition.flipped()] {
            if let Some(value) = self.condition_facts.get(&stored).copied() {
                used.cite(Proposition::ConditionIs(stored, value));
                return Some(value);
            }
        }
        if let Some((pointer, alignment)) = condition.as_pointer_alignment()
            && let Some((aligned, premise)) =
                self.pointer_alignment_certificate_decision(pointer, alignment)
        {
            if let Some(premise) = premise {
                used.cite(premise);
            }
            return Some(aligned);
        }
        if let ConditionTerm::PointerEqual(left, right) = condition {
            if left == right {
                return Some(true);
            }
            if left.blocks_proven_distinct(right) {
                return Some(false);
            }
        }
        if let ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        } = condition
            && used.depth < MAX_CITING_DEPTH
        {
            used.depth += 1;
            let nested = self.decide_pointer_word_equality_citing(left, right, used);
            used.depth -= 1;
            if let Some(decided) = nested {
                return Some(decided);
            }
        }
        // Shared mask equalities retain the same bound evidence as the
        // native pointer-word route above.
        if used.depth < MAX_CITING_DEPTH {
            used.depth += 1;
            let decided = self.decide_shared_mask_zero(condition, used);
            used.depth -= 1;
            if let Some(value) = decided {
                return Some(value);
            }
        }
        let decided = if used.fast_only {
            self.fast_leaf_decision(condition, &[])
        } else {
            self.decide(condition)
        };
        if decided.is_some() {
            used.complete = false;
        }
        decided
    }
}

/// A mask covering every possible tag bit. Symbolic tags use only exact
/// scalar bounds, so lookup work is independent of unrelated assumptions.
pub(in crate::kernel) fn tag_bound_citing(
    term: MachineOperandView<'_>,
    assumptions: &PureFactContext,
    used: &mut UsedFacts,
) -> Option<u64> {
    use crate::kernel::MachineCastSpelling as E;
    use MachineIntegerType as T;
    use MachineOperandView as V;
    if let Some(mask) = tag_bound(term) {
        return Some(mask);
    }
    let (format, value, signed) = match term.cast() {
        Some((E::UInt64FromInt32, T::Int32, T::UInt64, value)) => (T::Int32, value, true),
        Some((E::UInt64FromInt64, T::Int64, T::UInt64, value)) => (T::Int64, value, true),
        Some((E::UInt64From32, T::UInt32, T::UInt64, value)) => (T::UInt32, value, false),
        _ if term.variable().is_some()
            || matches!(term, V::Legacy(MachineTerm::MemoryLoad(..))) =>
        {
            (T::UInt64, term, false)
        }
        _ => return None,
    };
    let bounds = match format {
        T::Int32 => &assumptions.signed_order_bounds,
        T::UInt32 => &assumptions.uint32_order_bounds,
        T::Int64 => &assumptions.int64_signed_order_bounds,
        T::UInt64 => &assumptions.uint64_order_bounds,
        _ => unreachable!("tag bound format"),
    };
    let constant = |value| match format {
        T::Int32 | T::UInt32 => MachineTerm::constant(value),
        T::Int64 => MachineTerm::int64_constant(i64::from(value)),
        T::UInt64 => MachineTerm::uint64_constant(u64::from(value)),
        _ => unreachable!("tag bound format"),
    };
    // The common order index selects the original premise for this exact
    // non-strict edge. No other bounds or equality classes are searched.
    fn exact(
        bounds: &crate::kernel::assumptions::retained_order_bounds::OrderBoundIndex,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
        used: &mut UsedFacts,
    ) -> bool {
        if let Some(source) = bounds.exact_source(left, right, false) {
            used.cite(source.clone());
            true
        } else {
            false
        }
    }
    if signed && !exact(bounds, V::Legacy(&constant(0)), value, used) {
        return None;
    }
    for mask in [1u32, 3, 7] {
        if exact(bounds, value, V::Legacy(&constant(mask)), used) {
            return Some(u64::from(mask));
        }
    }
    None
}

fn require(
    form: &TaggedAddress,
    alignment: u64,
    operation: &str,
    assumptions: &PureFactContext,
    undecided: &mut Undecided<'_>,
    used: &mut UsedFacts,
) -> Result<bool, Refuted> {
    let conditions = [
        (
            ConditionTerm::pointer_aligned(form.pointer.clone(), alignment),
            format!("the pointer aligned to {alignment} bytes"),
        ),
        (
            ConditionTerm::uint64_less_than(
                form.tag.clone(),
                MachineTerm::uint64_constant(alignment),
            ),
            format!("the tag below {alignment}"),
        ),
    ];
    for (index, (condition, what)) in conditions.into_iter().enumerate() {
        if index == 1
            && tag_bound_citing(MachineOperandView::Legacy(&form.tag), assumptions, used)
                .is_some_and(|mask| mask < alignment)
        {
            continue;
        }
        match assumptions.decide_citing(&condition, used) {
            Some(true) => {}
            Some(false) => {
                return Err(Refuted(format!(
                    "{operation} on a tagged pointer address needs {what}, which is refuted"
                )));
            }
            None => match undecided {
                Undecided::Reject => return Ok(false),
                Undecided::Oblige(obligations) => {
                    let context = format!("{operation} on a tagged pointer address needs {what}");
                    if add_proof_obligation_with_context(
                        obligations,
                        assumptions,
                        Proposition::ConditionIs(condition, true),
                        Some(&context),
                    )
                    .is_none()
                    {
                        return Err(Refuted(format!("{context}, which is refuted")));
                    }
                }
            },
        }
    }
    Ok(true)
}

fn form_of(
    term: &MachineTerm,
    assumptions: &PureFactContext,
    undecided: &mut Undecided<'_>,
    used: &mut UsedFacts,
    through_facts: bool,
) -> Result<Option<TaggedAddress>, Refuted> {
    crate::instrumentation::record_deterministic_work(1);
    // A structural miss says nothing about an exact address equation for
    // the complete word. In particular, an opaque input of `word & ~mask`
    // must not hide a checked `(word & ~mask) == address(p)` premise.
    let direct = structural_form_of(term, assumptions, undecided, used, through_facts)?;
    if direct.is_some() || !through_facts {
        return Ok(direct);
    }
    // One exact recorded 64-bit equality may name the word's address form,
    // as a resource fact `word == address(next) + tag` does.
    for (equal, fact) in assumptions.recorded_uint64_equals(term) {
        if let Some(form) = form_of(&equal, assumptions, undecided, used, false)? {
            used.cite(Proposition::ConditionIs(fact, true));
            return Ok(Some(form));
        }
    }
    // Or one recorded about a word the equality graph proves equal to this
    // one: a read spelled through one alias, the fact through another. The
    // graph's equality is not a named premise, so the record cannot certify.
    for endpoint in assumptions
        .equality_graph
        .wide_equation_endpoints_equal_to(crate::kernel::MachineOperandView::Legacy(term))
    {
        crate::instrumentation::record_deterministic_work(1);
        if endpoint == *term {
            continue;
        }
        for (equal, fact) in assumptions.recorded_uint64_equals(&endpoint) {
            if let Some(form) = form_of(&equal, assumptions, undecided, used, false)? {
                used.cite(Proposition::ConditionIs(fact, true));
                used.complete = false;
                return Ok(Some(form));
            }
        }
    }
    Ok(None)
}

fn structural_form_of(
    term: &MachineTerm,
    assumptions: &PureFactContext,
    undecided: &mut Undecided<'_>,
    used: &mut UsedFacts,
    through_facts: bool,
) -> Result<Option<TaggedAddress>, Refuted> {
    let direct = match term {
        MachineTerm::PointerAddress(pointer, class) => Some(TaggedAddress {
            pointer: pointer.as_ref().clone(),
            object_class: class.class(),
            tag: MachineTerm::uint64_constant(0),
        }),
        MachineTerm::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Add,
            left,
            right,
        } => {
            if let Some(form) = form_of(left, assumptions, undecided, used, through_facts)? {
                Some(TaggedAddress {
                    pointer: form.pointer,
                    object_class: form.object_class,
                    tag: add_tag(form.tag, right.as_ref().clone()),
                })
            } else {
                form_of(right, assumptions, undecided, used, through_facts)?.map(|form| {
                    TaggedAddress {
                        pointer: form.pointer,
                        object_class: form.object_class,
                        tag: add_tag(left.as_ref().clone(), form.tag),
                    }
                })
            }
        }
        MachineTerm::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Subtract,
            left,
            right,
        } => {
            form_of(left, assumptions, undecided, used, through_facts)?.map(|form| TaggedAddress {
                pointer: form.pointer,
                object_class: form.object_class,
                tag: MachineTerm::uint64_subtract(form.tag, right.as_ref().clone()),
            })
        }
        MachineTerm::Binary {
            format: MachineIntegerType::UInt64,
            op: op @ (MachineBinaryOp::BitwiseAnd | MachineBinaryOp::BitwiseOr),
            left,
            right,
        } => {
            let operation = if *op == MachineBinaryOp::BitwiseAnd {
                CBitwiseOperation::And
            } else {
                CBitwiseOperation::Or
            };
            // The tag side is a constant, or for `|` a masked term `x & m`
            // (rbtree's `rb_color(rb) | (unsigned long)p`), whose bound the
            // mask constant gives.
            let masked_bound = |term: &MachineTerm, used: &mut UsedFacts| {
                tag_bound_citing(MachineOperandView::Legacy(term), assumptions, used)
            };
            let (inner, tag, constant) = match (left.uint64_as_const(), right.uint64_as_const()) {
                (None, Some(constant)) => (left, None, constant),
                (Some(constant), None) => (right, None, constant),
                (None, None) if matches!(operation, CBitwiseOperation::Or) => {
                    match (masked_bound(left, used), masked_bound(right, used)) {
                        (None, Some(bound)) => (left, Some(right.as_ref().clone()), bound),
                        (Some(bound), None) => (right, Some(left.as_ref().clone()), bound),
                        _ => return Ok(None),
                    }
                }
                _ => return Ok(None),
            };
            let Some(form) = form_of(inner, assumptions, undecided, used, through_facts)? else {
                return Ok(None);
            };
            match operation {
                CBitwiseOperation::And => {
                    let Some(alignment) = clearing_mask_alignment(constant) else {
                        return Ok(None);
                    };
                    if !require(
                        &form,
                        alignment,
                        "clearing tag bits",
                        assumptions,
                        undecided,
                        used,
                    )? {
                        return Ok(None);
                    }
                    Some(TaggedAddress {
                        pointer: form.pointer,
                        object_class: form.object_class,
                        tag: if tag_bound_citing(
                            MachineOperandView::Legacy(&form.tag),
                            assumptions,
                            used,
                        )
                        .is_some_and(|mask| mask & constant == 0)
                        {
                            MachineTerm::uint64_constant(0)
                        } else {
                            MachineTerm::uint64_bitwise_and(
                                form.tag,
                                MachineTerm::uint64_constant(constant),
                            )
                        },
                    })
                }
                CBitwiseOperation::Or => {
                    let Some(alignment) = constant
                        .checked_add(1)
                        .and_then(u64::checked_next_power_of_two)
                    else {
                        return Ok(None);
                    };
                    if constant != 0
                        && !require(
                            &form,
                            alignment,
                            "setting tag bits",
                            assumptions,
                            undecided,
                            used,
                        )?
                    {
                        return Ok(None);
                    }
                    Some(TaggedAddress {
                        pointer: form.pointer,
                        object_class: form.object_class,
                        tag: MachineTerm::uint64_bitwise_or(
                            form.tag,
                            tag.unwrap_or(MachineTerm::uint64_constant(constant)),
                        ),
                    })
                }
                CBitwiseOperation::Xor => None,
            }
        }
        _ => None,
    };
    Ok(direct)
}

/// `term` as `address(pointer) + tag` using only decided conditions.
pub(in crate::kernel) fn tagged_address_form(
    term: &MachineTerm,
    assumptions: &PureFactContext,
    used: &mut UsedFacts,
) -> Option<TaggedAddress> {
    form_of(term, assumptions, &mut Undecided::Reject, used, true)
        .ok()
        .flatten()
}

thread_local! {
    // Bounds depend only on syntax. Cache each shared node once per
    // verification, including misses, across changing proof contexts.
    static SHARED_TAG_BOUNDS: std::cell::RefCell<std::collections::HashMap<u64, Option<u64>>> = Default::default();
}

pub(in crate::kernel) fn clear_tag_bound_cache() {
    SHARED_TAG_BOUNDS.with(|cache| cache.borrow_mut().clear());
}

/// An upper bound on a tag term: a constant is its own bound, `x & m` is
/// bounded by `m`, and `a | b` by the all-ones value covering both bounds.
pub(in crate::kernel) fn tag_bound(term: MachineOperandView<'_>) -> Option<u64> {
    enum Task<'a> {
        Read(MachineOperandView<'a>),
        AfterLeft(Option<u64>, MachineOperandView<'a>),
        FinishOr(Option<u64>, u64),
    }
    // Match the native rule's literal roots. A constant arithmetic expression
    // is simplified by checking elsewhere, not by this tag-bound rule.
    let literal = |term: MachineOperandView<'_>| term.literal()?.uint64_as_const();
    SHARED_TAG_BOUNDS.with(|cache| {
        let mut cache = cache.borrow_mut();
        let mut pending = vec![Task::Read(term)];
        let mut values: Vec<Option<u64>> = Vec::new();
        while let Some(task) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let (key, result) = match task {
                Task::AfterLeft(key, right) => {
                    if let Some(left) = values.pop().expect("left tag bound") {
                        pending.push(Task::FinishOr(key, left));
                        pending.push(Task::Read(right));
                        continue;
                    }
                    (key, None)
                }
                Task::FinishOr(key, left) => {
                    let right = values.pop().expect("right tag bound");
                    let bound = right.and_then(|right| {
                        left.max(right)
                            .checked_add(1)?
                            .checked_next_power_of_two()
                            .map(|n| n - 1)
                    });
                    (key, bound)
                }
                Task::Read(term) => {
                    let key = match term {
                        MachineOperandView::Shared(term) => Some(term.id()),
                        MachineOperandView::Legacy(_) => None,
                    };
                    if let Some(key) = key
                        && let Some(bound) = cache.get(&key)
                    {
                        values.push(*bound);
                        continue;
                    }
                    let result = if let Some(value) = literal(term) {
                        Some(value)
                    } else {
                        match term.binary() {
                            Some((
                                MachineIntegerType::UInt64,
                                MachineBinaryOp::BitwiseAnd,
                                [left, right],
                            )) => literal(left).or_else(|| literal(right)),
                            Some((
                                MachineIntegerType::UInt64,
                                MachineBinaryOp::BitwiseOr,
                                [left, right],
                            )) => {
                                pending.push(Task::AfterLeft(key, right));
                                pending.push(Task::Read(left));
                                continue;
                            }
                            _ => None,
                        }
                    };
                    (key, result)
                }
            };
            if let Some(key) = key {
                cache.insert(key, result);
            }
            values.push(result);
        }
        values.pop().expect("root tag bound")
    })
}

/// `term & mask` with a tag-reading mask, as the masked tag alone, using
/// only decided conditions.
pub(in crate::kernel) fn masked_tag_value(
    term: &MachineTerm,
    assumptions: &PureFactContext,
    used: &mut UsedFacts,
) -> Option<MachineTerm> {
    let MachineTerm::Binary {
        format: MachineIntegerType::UInt64,
        op: MachineBinaryOp::BitwiseAnd,
        left,
        right,
    } = term
    else {
        return None;
    };
    let (inner, mask) = match (left.uint64_as_const(), right.uint64_as_const()) {
        (None, Some(mask)) => (left, mask),
        (Some(mask), None) => (right, mask),
        _ => return None,
    };
    let alignment = reading_mask_alignment(mask)?;
    let form = tagged_address_form(inner, assumptions, used)?;
    require(
        &form,
        alignment,
        "reading tag bits",
        assumptions,
        &mut Undecided::Reject,
        used,
    )
    .ok()
    .filter(|decided| *decided)?;
    let value = MachineTerm::uint64_bitwise_and(form.tag, MachineTerm::uint64_constant(mask));
    // A tag read that rewrites to itself makes no progress; deciding it
    // again would only recurse.
    (&value != term).then_some(value)
}

/// The pointer a 64-bit word converts back to: its recorded address with the
/// tag proven zero. Undecided alignment, tag-bound, and zero-tag conditions
/// become obligations; a refuted one is an error. `Ok(None)` means the word
/// has no recorded pointer origin.
pub(in crate::kernel) fn cast_tagged_address_to_pointer(
    term: &MachineTerm,
    assumptions: &PureFactContext,
    obligations: &mut Vec<ProofObligation>,
    target_type: CType,
) -> Result<Option<CPointerValue>, String> {
    let mut used = UsedFacts::new();
    let form = match form_of(
        term,
        assumptions,
        &mut Undecided::Oblige(obligations),
        &mut used,
        true,
    ) {
        Ok(Some(form)) => form,
        Ok(None) => return Ok(None),
        Err(Refuted(message)) => return Err(message),
    };
    let tag_is_zero =
        ConditionTerm::uint64_equal(form.tag.clone(), MachineTerm::uint64_constant(0));
    match assumptions.decide(&tag_is_zero) {
        Some(true) => Ok(Some(
            CPointerValue::new(form.pointer, target_type)
                .with_declared_object_class(form.object_class),
        )),
        Some(false) => Err(
            "integer-to-pointer cast of a tagged address requires the tag bits proven zero; \
             they are refuted"
                .to_string(),
        ),
        None => {
            let context = "integer-to-pointer cast of a tagged address requires the tag bits \
                           proven zero";
            if add_proof_obligation_with_context(
                obligations,
                assumptions,
                Proposition::ConditionIs(tag_is_zero, true),
                Some(context),
            )
            .is_none()
            {
                return Err(format!("{context}; they are refuted"));
            }
            Ok(Some(
                CPointerValue::new(form.pointer, target_type)
                    .with_declared_object_class(form.object_class),
            ))
        }
    }
}

#[cfg(test)]
mod exact_word_address_tests {
    use super::*;

    #[test]
    fn tag_bound_views_preserve_literal_masks_and_unknown_shapes() {
        use crate::kernel::{KernelTermExport, KernelTermImport};
        let _session = crate::kernel::VerificationSession::enter();
        let variable = || MachineTerm::Variable(Variable(985301));
        let constant = MachineTerm::uint64_constant;
        let binary = |format, op, left: MachineTerm, right: MachineTerm| MachineTerm::Binary {
            format,
            op,
            left: left.into(),
            right: right.into(),
        };
        let and = |left, right| {
            binary(
                MachineIntegerType::UInt64,
                MachineBinaryOp::BitwiseAnd,
                left,
                right,
            )
        };
        let or = |left, right| {
            binary(
                MachineIntegerType::UInt64,
                MachineBinaryOp::BitwiseOr,
                left,
                right,
            )
        };
        let cases = [
            (constant(0), Some(0)),
            (constant(u64::MAX), Some(u64::MAX)),
            (variable(), None),
            (and(variable(), constant(3)), Some(3)),
            (and(constant(3), variable()), Some(3)),
            (
                or(and(variable(), constant(1)), and(variable(), constant(3))),
                Some(3),
            ),
            (
                or(and(variable(), constant(0)), and(variable(), constant(0))),
                Some(0),
            ),
            (or(and(variable(), constant(1 << 63)), constant(1)), None),
            (or(variable(), and(variable(), constant(3))), None),
            (
                binary(
                    MachineIntegerType::UInt64,
                    MachineBinaryOp::Add,
                    constant(1),
                    constant(1),
                ),
                None,
            ),
            (
                and(
                    binary(
                        MachineIntegerType::UInt64,
                        MachineBinaryOp::Add,
                        constant(1),
                        constant(1),
                    ),
                    variable(),
                ),
                None,
            ),
            (
                binary(
                    MachineIntegerType::Int64,
                    MachineBinaryOp::BitwiseAnd,
                    variable(),
                    constant(3),
                ),
                None,
            ),
        ];
        for (native, expected) in cases {
            let root = KernelTermImport::default()
                .machine_arithmetic(MachineIntegerType::UInt64, &native)
                .unwrap();
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(
                tag_bound(MachineOperandView::Shared(&root)),
                expected,
                "shared {native:?}"
            );
            assert_eq!(
                tag_bound(MachineOperandView::Legacy(&native)),
                expected,
                "native {native:?}"
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    #[test]
    fn different_tags_on_aligned_addresses_need_no_pointer_inequality() {
        let _session = crate::kernel::VerificationSession::enter();
        let p = Pointer::symbolic(Variable(980030));
        let q = Pointer::symbolic(Variable(980031));
        let bare = PureFactContext::new();
        let aligned = bare
            .clone()
            .assume_condition(ConditionTerm::pointer_aligned(p.clone(), 8), true)
            .assume_condition(ConditionTerm::pointer_aligned(q.clone(), 8), true);
        let word = |pointer: Pointer, tag| {
            MachineTerm::uint64_add(
                MachineTerm::pointer_address(pointer),
                MachineTerm::uint64_constant(tag),
            )
        };
        let mut used = UsedFacts::new();
        assert_eq!(
            aligned.decide_pointer_word_equality_citing(
                &word(p.clone(), 1),
                &word(q.clone(), 0),
                &mut used,
            ),
            Some(false)
        );
        assert!(used.complete);
        assert_eq!(used.premises.len(), 2);
        // Neither missing alignment nor equal tags establish inequality.
        assert_eq!(
            bare.decide_pointer_word_equality_citing(
                &word(p.clone(), 1),
                &word(q.clone(), 0),
                &mut UsedFacts::new(),
            ),
            None
        );
        assert_eq!(
            aligned.decide_pointer_word_equality_citing(
                &word(p, 1),
                &word(q, 1),
                &mut UsedFacts::new(),
            ),
            None
        );
    }

    #[test]
    fn classed_and_bare_spellings_of_one_address_are_one_term() {
        use crate::kernel::effective_type::{CAccessClass, CStructClass};
        use std::hash::{Hash, Hasher};
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::symbolic(Variable(980120));
        let other = Pointer::symbolic(Variable(980121));
        let class = CAccessClass::Struct(CStructClass::opaque("node"));
        let classed = MachineTerm::object_pointer_address(pointer.clone(), Some(class.clone()));
        let bare = MachineTerm::pointer_address(pointer.clone());
        assert_eq!(classed, bare);
        assert_eq!(classed.cmp(&bare), std::cmp::Ordering::Equal);
        let hash = |term: &MachineTerm| {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            term.hash(&mut hasher);
            hasher.finish()
        };
        assert_eq!(hash(&classed), hash(&bare));
        // A premise stated over the classed spelling is the exact fact a
        // query over the bare spelling asks for, in either polarity.
        let stated = ConditionTerm::uint64_equal(
            classed.clone(),
            MachineTerm::pointer_address(other.clone()),
        );
        let asked = ConditionTerm::uint64_equal(bare.clone(), MachineTerm::pointer_address(other));
        let assumptions = PureFactContext::new().assume_condition(stated, false);
        assert!(
            crate::kernel::reasoning::path_facts::required_obligation_is_exactly_discharged(
                &assumptions,
                &Proposition::ConditionIs(asked, false),
            )
        );
        // The class is evidence for decoding, and identity never erases it.
        let MachineTerm::PointerAddress(_, retained) = &classed else {
            panic!("an address term");
        };
        assert_eq!(retained.class(), Some(class));
    }

    #[test]
    fn an_alignment_premise_over_a_classed_address_is_cited_as_admitted() {
        use crate::kernel::effective_type::{CAccessClass, CStructClass};
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::symbolic(Variable(980110));
        let class = CAccessClass::Struct(CStructClass::opaque("node"));
        let premise = ConditionTerm::uint64_equal(
            MachineTerm::uint64_bitwise_and(
                MachineTerm::object_pointer_address(pointer.clone(), Some(class.clone())),
                MachineTerm::uint64_constant(7),
            ),
            MachineTerm::uint64_constant(0),
        );
        let assumptions = PureFactContext::new().assume_condition(premise.clone(), true);
        let (aligned, cited) = assumptions
            .pointer_alignment_certificate_decision(&pointer, 8)
            .unwrap();
        assert!(aligned);
        assert_eq!(cited, Some(Proposition::ConditionIs(premise, true)));
        for address in [
            MachineTerm::pointer_address(pointer.clone()),
            MachineTerm::object_pointer_address(pointer.clone(), Some(class.clone())),
        ] {
            let tagged = ConditionTerm::uint64_equal(
                MachineTerm::uint64_bitwise_or(address.clone(), MachineTerm::uint64_constant(1)),
                MachineTerm::uint64_add(address, MachineTerm::uint64_constant(1)),
            );
            assert_eq!(assumptions.decide(&tagged), Some(true));
        }
    }

    #[test]
    fn encoded_object_class_survives_tags_and_a_different_cast_type() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::symbolic(Variable(980010));
        let class = CAccessClass::Scalar(CScalarClass::Int);
        let assumptions = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_aligned(pointer.clone(), 4), true);
        let mut obligations = Vec::new();
        let encoded = cast_c_value_to_type(
            CValue::Pointer(
                CPointerValue::new(pointer.clone(), CType::Int32Pointer)
                    .with_object_class(Some(class.clone())),
            ),
            CType::UInt64,
            IntegerConversion::Modular,
            &mut obligations,
            &assumptions,
        )
        .unwrap();
        let decoded = cast_c_value_to_type(
            encoded.clone(),
            CType::Float64Pointer,
            IntegerConversion::Modular,
            &mut obligations,
            &assumptions,
        )
        .unwrap();
        assert!(
            matches!(decoded, CValue::Pointer(ref value) if value.object_class() == Some(class.clone()))
        );
        let CValue::UInt64(address) = encoded.numeric_value() else {
            panic!("encoded address")
        };
        let address = address.clone();
        let tagged =
            MachineTerm::uint64_bitwise_or(address.clone(), MachineTerm::uint64_constant(1));
        let cleared =
            MachineTerm::uint64_bitwise_and(tagged.clone(), MachineTerm::uint64_constant(!3));
        let subtracted = MachineTerm::uint64_subtract(
            MachineTerm::uint64_add(address.clone(), MachineTerm::uint64_constant(1)),
            MachineTerm::uint64_constant(1),
        );
        for word in [address.clone(), cleared, subtracted] {
            // The numeric decoder recovers only coordinates and object class.
            // A cast producer separately supplies the complete value identity.
            let decoded = cast_tagged_address_to_pointer(
                &word,
                &assumptions,
                &mut obligations,
                CType::Float64Pointer,
            )
            .unwrap()
            .unwrap();
            assert_eq!(decoded.pointer(), &pointer);
            assert_eq!(decoded.object_class(), Some(class.clone()));
            assert_eq!(decoded.c_type(), CType::Float64Pointer);
        }
        assert!(
            cast_tagged_address_to_pointer(
                &tagged,
                &assumptions,
                &mut obligations,
                CType::Int32Pointer
            )
            .is_err()
        );
        assert!(obligations.is_empty());
        assert_eq!(
            assumptions.decide(&ConditionTerm::uint64_equal(
                address,
                MachineTerm::pointer_address(pointer)
            )),
            Some(true)
        );
    }

    #[test]
    fn object_class_recovery_uses_only_available_origin_evidence() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::symbolic(Variable(980020));
        let class = CAccessClass::Scalar(CScalarClass::Int);
        let word = MachineTerm::Variable(Variable(980021));
        let premise = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                word.clone(),
                MachineTerm::object_pointer_address(pointer.clone(), Some(class.clone())),
            ),
            true,
        );
        let parent = PureFactContext::new();
        let branch = parent.clone().assume_proposition(premise.clone());
        let mut obligations = Vec::new();
        let decoded =
            cast_tagged_address_to_pointer(&word, &branch, &mut obligations, CType::Float64Pointer)
                .unwrap()
                .unwrap();
        assert_eq!(decoded.pointer(), &pointer);
        assert_eq!(decoded.object_class(), Some(class));
        for context in [
            parent,
            branch.without_exact_fact(&premise),
            branch.restricted_to_facts(&[], &[]),
        ] {
            assert!(
                cast_tagged_address_to_pointer(
                    &word,
                    &context,
                    &mut obligations,
                    CType::Float64Pointer
                )
                .unwrap()
                .is_none()
            );
        }
        let bare = cast_tagged_address_to_pointer(
            &MachineTerm::pointer_address(pointer),
            &PureFactContext::new(),
            &mut obligations,
            CType::Float64Pointer,
        )
        .unwrap()
        .unwrap();
        assert_eq!(
            bare.object_class(),
            None,
            "the target cast must not invent a class"
        );
        assert!(obligations.is_empty());
    }

    #[test]
    fn compound_word_address_requires_origin_and_stops_at_cyclic_equations() {
        let _session = crate::kernel::VerificationSession::enter();
        let expression = MachineTerm::uint64_bitwise_and(
            MachineTerm::Variable(Variable(980001)),
            MachineTerm::uint64_constant(!3),
        );
        let alias = MachineTerm::Variable(Variable(980002));
        for assumptions in [
            PureFactContext::new(),
            PureFactContext::new()
                .assume_condition(ConditionTerm::uint64_equal(expression.clone(), alias), true),
        ] {
            let mut obligations = Vec::new();
            assert_eq!(
                cast_tagged_address_to_pointer(
                    &expression,
                    &assumptions,
                    &mut obligations,
                    CType::Int32Pointer
                )
                .unwrap(),
                None
            );
            assert!(obligations.is_empty());
        }
    }

    #[test]
    fn shared_tag_bound_guards_preserve_sources_width_and_scope() {
        use crate::kernel::{KernelTermExport, KernelTermImport};
        use MachineCastSpelling as E;
        use MachineIntegerType as T;
        for (format, encoding, signed) in [
            (T::Int32, E::UInt64FromInt32, true),
            (T::Int64, E::UInt64FromInt64, true),
            (T::UInt32, E::UInt64From32, false),
        ] {
            for mirrored in [false, true] {
                let _session = crate::kernel::VerificationSession::enter();
                let value = MachineTerm::Binary {
                    format,
                    op: MachineBinaryOp::Add,
                    left: MachineTerm::Variable(Variable(985321)).into(),
                    right: MachineTerm::Variable(Variable(985322)).into(),
                };
                let constant = |n| {
                    crate::kernel::machine_integer::range::constant_word(
                        format,
                        &num_bigint::BigInt::from(n),
                    )
                    .unwrap()
                };
                let mut lower = ConditionTerm::machine_compare(
                    format,
                    CompareRelation::LessEqual,
                    constant(0),
                    value.clone(),
                );
                let mut upper = ConditionTerm::machine_compare(
                    format,
                    CompareRelation::LessEqual,
                    value.clone(),
                    constant(3),
                );
                if mirrored {
                    lower = lower.flipped();
                    upper = upper.flipped();
                }
                let converted = MachineTerm::legacy_cast(encoding, value.into());
                let shared = KernelTermImport::default()
                    .machine_arithmetic(T::UInt64, &converted)
                    .unwrap();
                for lower_truth in [None, Some(false), Some(true)] {
                    if !signed && lower_truth.is_some() {
                        continue;
                    }
                    for upper_truth in [None, Some(false), Some(true)] {
                        let parent = PureFactContext::new();
                        let mut context = parent.clone();
                        if let Some(truth) = lower_truth {
                            context = context.assume_condition(lower.clone(), truth);
                        }
                        if let Some(truth) = upper_truth {
                            context = context.assume_condition(upper.clone(), truth);
                        }
                        let expected = (upper_truth == Some(true)
                            && (!signed || lower_truth == Some(true)))
                        .then_some(3);
                        let exports = KernelTermExport::machine_export_count();
                        for view in [
                            MachineOperandView::Shared(&shared),
                            MachineOperandView::Legacy(&converted),
                        ] {
                            let mut used = UsedFacts::new();
                            assert_eq!(
                                tag_bound_citing(view, &context, &mut used),
                                expected,
                                "{format:?}, {lower_truth:?}, {upper_truth:?}, mirrored={mirrored}"
                            );
                            if expected.is_some() {
                                assert!(
                                    used.premises
                                        .contains(&Proposition::ConditionIs(upper.clone(), true))
                                );
                                if signed {
                                    assert!(
                                        used.premises.contains(&Proposition::ConditionIs(
                                            lower.clone(),
                                            true
                                        ))
                                    );
                                }
                                assert!(
                                    used.complete
                                        && used
                                            .premises
                                            .iter()
                                            .all(|p| context.contains_assumed_exact(p))
                                );
                                let withdrawn = context.without_exact_fact(
                                    &Proposition::ConditionIs(upper.clone(), true),
                                );
                                assert_eq!(
                                    tag_bound_citing(view, &withdrawn, &mut UsedFacts::new()),
                                    None
                                );
                            }
                            assert_eq!(
                                tag_bound_citing(view, &parent, &mut UsedFacts::new()),
                                None
                            );
                        }
                        assert_eq!(KernelTermExport::machine_export_count(), exports);
                    }
                }
            }
        }
    }

    #[test]
    fn symbolic_tag_bounds_require_nonnegative_and_upper_premises() {
        let _session = crate::kernel::VerificationSession::enter();
        let tag = MachineTerm::Variable(Variable(980_011));
        let converted =
            MachineTerm::legacy_cast(MachineCastSpelling::UInt64FromInt32, Box::new(tag.clone()));
        let lower = ConditionTerm::signed_less_equal(0u32.into(), tag.clone());
        let upper = ConditionTerm::signed_less_equal(tag, 1u32.into());
        for context in [
            PureFactContext::new(),
            PureFactContext::new().assume_condition(lower.clone(), true),
            PureFactContext::new().assume_condition(upper.clone(), true),
        ] {
            assert_eq!(
                tag_bound_citing(
                    MachineOperandView::Legacy(&converted),
                    &context,
                    &mut UsedFacts::new()
                ),
                None
            );
        }
        let pointer = Pointer::symbolic(Variable(980_012));
        let context = PureFactContext::new()
            .assume_condition(lower.clone(), true)
            .assume_condition(upper.clone(), true)
            .assume_condition(ConditionTerm::pointer_aligned(pointer.clone(), 8), true);
        let tagged = MachineTerm::uint64_bitwise_or(
            MachineTerm::pointer_address(pointer.clone()),
            converted,
        );
        let cleared = MachineTerm::uint64_bitwise_and(tagged, MachineTerm::uint64_constant(!3));
        let mut used = UsedFacts::new();
        let form = tagged_address_form(&cleared, &context, &mut used).unwrap();
        assert_eq!(form.pointer, pointer);
        assert_eq!(form.tag.uint64_as_const(), Some(0));
        assert!(used.complete);
        for condition in [lower, upper] {
            assert!(
                used.premises
                    .contains(&Proposition::ConditionIs(condition, true))
            );
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/eval/pointer_tags/exact_word_address_tests.rs");
    }
}
