//! The legacy-walk audit (`click audit legacy-walk`): every query that names
//! a read with the assumption-free version walk over memory snapshots
//! ([`super::last_same_version_point`] and the entries beside it).
//!
//! Reads are moving from that walk to versions a program point carries
//! (`roadmap/smart-tactics.md`, "Program-point memory migration"), and the
//! walk is to be deleted. The walk costs history per new cell, so it is also
//! the step cost that grows with earlier statements. The audit counts what
//! still reaches it, by calling site, resource and storage, so the remaining
//! routes can be migrated in order of traffic and the walk deleted once the
//! count is zero.
//!
//! A query is counted at the outermost entry only: a walk one entry makes
//! through another is part of the first query. Each record also carries the
//! deterministic work the query charged, which is zero where its caller
//! runs uncharged. The audit is uncharged and never decides.

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::panic::Location;

use super::TrackedResource;
use crate::kernel::primitives::AddressBase;

/// What one group of queries shares.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct QueryKind {
    site: String,
    resource: &'static str,
    storage: &'static str,
    extent: String,
}

/// How many queries of one kind a thread made, and the work they charged.
#[derive(Clone, Copy, Debug, Default)]
struct Tally {
    queries: usize,
    work: usize,
}

/// One thread's tallies, written as records when the thread ends. The audit
/// verifies each container on a thread of its own, named after it.
#[derive(Default)]
struct ThreadTallies(BTreeMap<QueryKind, Tally>);

impl Drop for ThreadTallies {
    fn drop(&mut self) {
        let records = render(&self.0, &thread_name());
        if !records.is_empty() {
            crate::instrumentation::LEGACY_WALK_RECORDS.write(&records);
        }
    }
}

thread_local! {
    /// Nonzero inside a counted query, so its inner entries are not counted.
    static DEPTH: Cell<u32> = const { Cell::new(0) };
    static TALLIES: RefCell<ThreadTallies> = RefCell::new(ThreadTallies::default());
}

#[cfg(test)]
thread_local! {
    static CAPTURE: RefCell<Option<BTreeMap<QueryKind, Tally>>> = const { RefCell::new(None) };
}

fn enabled() -> bool {
    #[cfg(test)]
    if CAPTURE.with(|capture| capture.borrow().is_some()) {
        return true;
    }
    crate::instrumentation::LEGACY_WALK_RECORDS.enabled()
}

/// Runs `walk`, a legacy version walk asked about `resource`, counting it
/// against the caller of the entry that called this.
#[track_caller]
pub(super) fn counted<R>(resource: &TrackedResource<'_>, walk: impl FnOnce() -> R) -> R {
    if DEPTH.with(Cell::get) > 0 || !enabled() {
        return walk();
    }
    let site = Location::caller();
    struct Leave;
    impl Drop for Leave {
        fn drop(&mut self) {
            DEPTH.with(|depth| depth.set(depth.get() - 1));
        }
    }
    DEPTH.with(|depth| depth.set(depth.get() + 1));
    let leave = Leave;
    let (result, work) = crate::instrumentation::measure_deterministic_work(walk);
    drop(leave);
    let kind = kind_of(site, resource);
    let add = |tallies: &mut BTreeMap<QueryKind, Tally>| {
        let tally = tallies.entry(kind.clone()).or_default();
        tally.queries += 1;
        tally.work += work;
    };
    #[cfg(test)]
    if CAPTURE.with(|capture| capture.borrow_mut().as_mut().map(add).is_some()) {
        return result;
    }
    TALLIES.with(|tallies| add(&mut tallies.borrow_mut().0));
    result
}

fn kind_of(site: &Location<'_>, resource: &TrackedResource<'_>) -> QueryKind {
    let (resource, storage, extent) = match resource {
        TrackedResource::Cell { pointer, bytes } => {
            ("cell", storage_of(&pointer.base), bytes.to_string())
        }
        TrackedResource::Block(block) => ("block", storage_of(block), String::new()),
        TrackedResource::Ranges(_) => ("ranges", "", String::new()),
        TrackedResource::AnyMemory => ("any memory", "", String::new()),
        TrackedResource::ModelField { .. } => ("model field", "", String::new()),
    };
    QueryKind {
        site: format!("{}:{}", site.file(), site.line()),
        resource,
        storage,
        extent,
    }
}

/// The storage class a read's block belongs to, as the point indexes
/// distinguish them.
fn storage_of(block: &AddressBase) -> &'static str {
    if block.is_static_storage_block() {
        return "static";
    }
    if block.is_havoc_block() {
        return "havoc";
    }
    match block {
        AddressBase::Concrete(_) => "concrete",
        AddressBase::StringLiteral { .. } => "string literal",
        AddressBase::Function(_) | AddressBase::FunctionSymbolic(_) => "function",
        AddressBase::ExternalArgument | AddressBase::ExternalObject(_) => "external",
        AddressBase::Symbolic(_) => "symbolic",
        AddressBase::Load(_) => "loaded pointer",
        AddressBase::PureFunctionApplication(_) => "pure application",
        AddressBase::Heap(_) => "heap",
        AddressBase::Temporary(_) => "temporary",
        AddressBase::AutomaticLocal { .. } => "automatic",
        _ => "other",
    }
}

/// The records of `tallies`, one line per kind:
/// `queries<TAB>work<TAB>site<TAB>resource<TAB>storage<TAB>extent<TAB>container`.
fn render(tallies: &BTreeMap<QueryKind, Tally>, container: &str) -> String {
    tallies
        .iter()
        .map(|(kind, tally)| {
            format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{container}\n",
                tally.queries, tally.work, kind.site, kind.resource, kind.storage, kind.extent
            )
        })
        .collect()
}

/// The running thread's name, which names the container under
/// `click audit legacy-walk`.
fn thread_name() -> String {
    std::thread::current().name().unwrap_or("").to_string()
}

/// The records `operation`'s queries would write, instead of writing them.
#[cfg(test)]
pub(crate) fn capture(operation: impl FnOnce()) -> String {
    let previous = CAPTURE.with(|capture| capture.replace(Some(BTreeMap::new())));
    operation();
    let tallies = CAPTURE
        .with(|capture| capture.replace(previous))
        .unwrap_or_default();
    render(&tallies, "")
}
