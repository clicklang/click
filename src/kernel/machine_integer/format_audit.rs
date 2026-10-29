//! The signedness audit: where the kernel still reads an `int32` and a
//! `uint32` value, or a narrow value and its 32-bit word, as one word.
//!
//! `design/machine-integers.md` ("Every format its own nodes", Decisions,
//! 2026-10-29) replaces that word identity (rules K1, K2, K5, K6 and K8,
//! and the narrow word) with nodes of each format and e-graph relations
//! between them. Before any term changes, this audit records every place
//! the identity is used, so the proofs that depend on it are known.
//!
//! Setting `CLICK_FORMAT_AUDIT=<path>` in a debug build appends one line per
//! distinct use: the kind ([`WordIdentity`]), the source site that used it,
//! the running thread (which names the mdtest or example under
//! `scripts/format-audit.sh`), and the claim and tactic being checked.
//! Each distinct line is written once per process. The audit only observes:
//! it charges no work and never changes a term, a decision or an output.
//! A release build records nothing.

#[cfg(debug_assertions)]
use std::io::Write;

/// One use of the word identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum WordIdentity {
    /// A sign cast σ removed from an operand, so the operand's word stands
    /// for the cast (rules K1 to K4).
    SignCastPeeled,
    /// The widening of an 8- or 16-bit value into 32 bits removed from an
    /// operand, so the narrow value's word stands for it (rule K8).
    WideningPeeled,
    /// A `uint32` constant read as the `int32` constant of its bits (K1).
    UInt32ConstantPeeled,
    /// A sign-free `uint32` operation (`+ - * << & | ^ ~`) built as the
    /// `int32` node of its words (the 32-bit operator merge).
    UInt32OperatorAtInt32,
    /// A `uint32` equality filed as the `int32` one (rule K6).
    UInt32EqualityAtInt32,
    /// A `uint32` read named by its word's `int32` read (rule K5's naming).
    UInt32ReadNamedByInt32,
    /// A C widening between narrow formats that keeps the operand's term
    /// under the wider format's tag.
    NarrowWordReused,
    /// A narrow value observed whose term is a 32-bit operation's word
    /// rather than a value of its format.
    NarrowValueAsWord,
    /// Rust narrow arithmetic lowered as a 32-bit operation and a cast back.
    PromotedNarrowArithmetic,
}

impl WordIdentity {
    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::SignCastPeeled => "sign-cast-peeled",
            Self::WideningPeeled => "widening-peeled",
            Self::UInt32ConstantPeeled => "uint32-constant-peeled",
            Self::UInt32OperatorAtInt32 => "uint32-operator-at-int32",
            Self::UInt32EqualityAtInt32 => "uint32-equality-at-int32",
            Self::UInt32ReadNamedByInt32 => "uint32-read-named-by-int32",
            Self::NarrowWordReused => "narrow-word-reused",
            Self::NarrowValueAsWord => "narrow-value-as-word",
            Self::PromotedNarrowArithmetic => "promoted-narrow-arithmetic",
        }
    }
}

/// Whether `term`'s root is a sign-free 32-bit operator (`+ - * << & | ^`
/// or `~`), which the term arena files at `int32` whatever the signedness
/// of the value it computes. One match on the root.
pub(crate) fn is_sign_free_word_operator(term: &crate::kernel::Bitvector32Term) -> bool {
    use crate::kernel::{MachineBinaryOp as Op, MachineIntegerType as Ty};
    matches!(
        term,
        crate::kernel::Bitvector32Term::Binary {
            format: Ty::Int32,
            op: Op::Add
                | Op::Subtract
                | Op::Multiply
                | Op::ShiftLeft
                | Op::BitwiseAnd
                | Op::BitwiseOr
                | Op::BitwiseXor,
            ..
        } | crate::kernel::Bitvector32Term::Unary {
            format: Ty::Int32,
            ..
        }
    )
}

#[cfg(all(test, debug_assertions))]
thread_local! {
    static CAPTURE: std::cell::RefCell<Option<Vec<String>>> = const { std::cell::RefCell::new(None) };
}

/// Runs `run` with the audit recording to memory, and returns its lines in
/// the order they were first recorded.
#[cfg(all(test, debug_assertions))]
pub(crate) fn capture(run: impl FnOnce()) -> Vec<String> {
    CAPTURE.with(|lines| lines.replace(Some(Vec::new())));
    run();
    CAPTURE.with(|lines| lines.take()).unwrap_or_default()
}

/// Whether the audit records. One load of a cached flag, so the hooks cost
/// nothing measurable when it is off.
#[cfg(debug_assertions)]
fn enabled() -> bool {
    #[cfg(test)]
    if CAPTURE.with(|lines| lines.borrow().is_some()) {
        return true;
    }
    crate::instrumentation::format_audit_sink().is_some()
}

/// Records one use of the word identity at `site`. A no-op unless the
/// audit is on, and always in a release build.
#[inline]
pub(crate) fn record(kind: WordIdentity, site: &'static std::panic::Location<'static>) {
    #[cfg(debug_assertions)]
    if enabled() {
        write(kind, site);
    }
    #[cfg(not(debug_assertions))]
    let _ = (kind, site);
}

#[cfg(debug_assertions)]
fn write(kind: WordIdentity, site: &'static std::panic::Location<'static>) {
    let thread = std::thread::current().name().unwrap_or("").to_string();
    let (claim, tactic) = crate::instrumentation::active_claim_and_tactic();
    let line = format!(
        "{}\t{}:{}\t{thread}\t{}\t{}\n",
        kind.name(),
        site.file(),
        site.line(),
        clean(&claim),
        clean(&tactic),
    );
    #[cfg(test)]
    if CAPTURE.with(|lines| {
        lines
            .borrow_mut()
            .as_mut()
            .map(|lines| {
                if !lines.contains(&line) {
                    lines.push(line.clone());
                }
            })
            .is_some()
    }) {
        return;
    }
    static SEEN: std::sync::Mutex<Option<std::collections::HashSet<String>>> =
        std::sync::Mutex::new(None);
    let fresh = SEEN
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .get_or_insert_with(Default::default)
        .insert(line.clone());
    if fresh
        && let Some(sink) = crate::instrumentation::format_audit_sink()
        && let Ok(mut file) = sink.lock()
    {
        let _ = file.write_all(line.as_bytes());
    }
}

#[cfg(debug_assertions)]
fn clean(text: &str) -> String {
    text.chars()
        .map(|c| if c == '\t' || c == '\n' { ' ' } else { c })
        .take(200)
        .collect()
}

#[cfg(all(test, debug_assertions))]
mod tests {
    use super::*;
    use crate::kernel::{Bitvector32Term, CValue, IntegerTerm, MachineIntegerType, Variable};

    fn kinds(lines: &[String]) -> Vec<&str> {
        lines
            .iter()
            .map(|line| line.split('\t').next().unwrap_or(""))
            .collect()
    }

    /// Building a 32-bit operator over σ and a `uint32` constant records
    /// both peels; an operator over plain `int32` operands records nothing.
    #[test]
    fn an_operator_over_a_sign_cast_and_a_uint32_constant_records_both_peels() {
        let x = Bitvector32Term::Variable(Variable(1));
        let plain = capture(|| {
            let _ = Bitvector32Term::add(x.clone(), Bitvector32Term::Constant(1));
        });
        assert!(plain.is_empty(), "{plain:?}");
        let sigma = Bitvector32Term::sign_cast32(
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            x.clone(),
        );
        let lines = capture(|| {
            let _ = Bitvector32Term::add(sigma, Bitvector32Term::UInt32Constant(1));
        });
        let kinds = kinds(&lines);
        assert!(kinds.contains(&"sign-cast-peeled"), "{lines:?}");
        assert!(kinds.contains(&"uint32-constant-peeled"), "{lines:?}");
        // The site is the constructor that peeled, not the audit itself.
        assert!(
            lines.iter().all(|line| line.contains("term_operations.rs")),
            "{lines:?}"
        );
    }

    /// A `uint32` value whose term is an `int32` sign-free operator, and a
    /// `uint32` equality, record their identities; the `int32` ones do not.
    #[test]
    fn a_uint32_sum_and_a_uint32_equality_record_their_int32_filing() {
        let (a, b) = (
            Bitvector32Term::Variable(Variable(1)),
            Bitvector32Term::Variable(Variable(2)),
        );
        let signed = capture(|| {
            let _ = crate::kernel::int32(Bitvector32Term::add(a.clone(), b.clone()));
            let _ = crate::kernel::ConditionTerm::equal(a.clone(), b.clone());
        });
        assert!(signed.is_empty(), "{signed:?}");
        let lines = capture(|| {
            let _ = crate::kernel::uint32(Bitvector32Term::add(a.clone(), b.clone()));
            let _ = crate::kernel::ConditionTerm::uint32_equal(a.clone(), b.clone());
        });
        let kinds = kinds(&lines);
        assert!(kinds.contains(&"uint32-operator-at-int32"), "{lines:?}");
        assert!(kinds.contains(&"uint32-equality-at-int32"), "{lines:?}");
    }

    /// A narrow observation of a 32-bit sum records it; a narrow
    /// observation of a variable does not.
    #[test]
    fn a_narrow_observation_of_a_word_sum_records_it() {
        let a = Bitvector32Term::Variable(Variable(1));
        let plain = capture(|| {
            let _ = IntegerTerm::from_machine(MachineIntegerType::UInt8, a.clone());
        });
        assert!(plain.is_empty(), "{plain:?}");
        let lines = capture(|| {
            let _ = IntegerTerm::from_machine(
                MachineIntegerType::UInt8,
                Bitvector32Term::add(a.clone(), Bitvector32Term::Constant(1)),
            );
        });
        assert_eq!(kinds(&lines), vec!["narrow-value-as-word"], "{lines:?}");
    }

    /// The audit observes only: a value built with it on is the value built
    /// with it off, and costs the same deterministic work.
    #[test]
    fn the_audit_changes_no_term_and_no_work() {
        let build = || {
            let sigma = Bitvector32Term::sign_cast32(
                MachineIntegerType::UInt32,
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(Variable(3)),
            );
            crate::kernel::uint32(Bitvector32Term::multiply(
                sigma,
                Bitvector32Term::UInt32Constant(7),
            ))
        };
        let (off, off_work) = crate::instrumentation::measure_deterministic_work(build);
        let mut on = None;
        let lines =
            capture(|| on = Some(crate::instrumentation::measure_deterministic_work(build)));
        let (on, on_work) = on.unwrap();
        assert!(!lines.is_empty());
        assert_eq!(on, off);
        assert_eq!(on_work, off_work);
        assert!(matches!(on, CValue::UInt32(_)));
    }
}
