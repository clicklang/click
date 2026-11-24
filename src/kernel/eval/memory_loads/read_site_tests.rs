//! A memory-named pointer load records where it was made
//! (`design/point-named-reads.md`, stage 1) without changing its term: each
//! producer below, given a site, builds the load its siteless call builds.
//! Each check reads its own cell, so no earlier interning or cached
//! selection supplies the load it inspects.

use super::*;
use crate::kernel::{Variable, VerificationSession};

/// The point a read is made at, on a path, and the memory it stands for.
fn site() -> (SymbolicMemory, ProgramPoint) {
    let memory = SymbolicMemory::new();
    let site = ProgramPoint::starting_at(&memory);
    assert!(site.id().is_some(), "a point on a path");
    (memory, site)
}

fn cell(id: u64) -> Address {
    Address::symbolic(Variable(id))
}

/// Whether the load `address` is based on recorded `site` as its read site.
fn records(address: &Address, site: &ProgramPoint) -> bool {
    address.as_loaded_value().is_some_and(|read| {
        read.point.read_version_id().is_none()
            && read
                .point
                .read_site()
                .is_some_and(|path| path.id() == site.id())
    })
}

/// The sited load, built first, carries the site; the siteless call names
/// the same load, in equality and in order.
fn same_load(sited: &Address, bare: &Address, site: &ProgramPoint) {
    assert!(records(sited, site), "the read records its site: {sited:?}");
    assert_eq!(sited, bare);
    assert_eq!(sited.cmp(bare), std::cmp::Ordering::Equal);
}

fn pointer(value: ProgramValue) -> Pointer {
    let ProgramValue::Pointer(pointer) = value else {
        panic!("a pointer read: {value:?}");
    };
    pointer
}

#[test]
fn a_memory_named_load_records_its_site_and_is_the_same_load() {
    let _session = VerificationSession::enter();
    let (_, site) = site();
    let memory = site.shared_memory().clone();
    let at = cell(1_207_001);
    let sited = Address::loaded_value_read_at(&memory, Some(&site), &at);
    same_load(&sited, &Address::loaded_value(&memory, &at), &site);
    let at = cell(1_207_002);
    let sited = Address::loaded_value_at(&site, &at);
    same_load(&sited, &Address::loaded_value(&memory, &at), &site);
}

#[test]
fn a_canonical_pointer_read_records_its_site_and_is_the_same_read() {
    let _session = VerificationSession::enter();
    let (_, site) = site();
    let memory = site.shared_memory().clone();
    let at = cell(1_207_011);
    let sited = Address::canonical_read(&memory, Some(&site), &at);
    same_load(&sited, &Address::canonical_read(&memory, None, &at), &site);
}

#[test]
fn a_version_read_records_its_site_and_is_the_same_read() {
    let _session = VerificationSession::enter();
    let (_, site) = site();
    let memory = site.shared_memory().clone();
    let at = cell(1_207_021);
    let sited = Address::version_read_at(&memory, Some(&site), &at);
    same_load(&sited, &Address::version_read(&memory, &at), &site);
}

#[test]
fn symbolic_pointer_loads_record_their_site_and_are_the_same_values() {
    let _session = VerificationSession::enter();
    let (memory, site) = site();
    let ty = ProgramType::Int32Pointer;
    let at = cell(1_207_031);
    let sited = pointer(memory.symbolic_pointer_load(Some(&site), &at, ty));
    let bare = pointer(memory.symbolic_pointer_load(None, &at, ty));
    same_load(sited.address(), bare.address(), &site);
    same_load(sited.provenance(), bare.provenance(), &site);
    assert_eq!(sited, bare);

    let at = cell(1_207_032);
    let sited = pointer(memory.symbolic_pointer_version_load(Some(&site), &at, ty));
    let bare = pointer(memory.symbolic_pointer_version_load(None, &at, ty));
    same_load(sited.address(), bare.address(), &site);
    assert_eq!(sited, bare);

    let at = cell(1_207_033);
    let sited = pointer(symbolic_storage_cell_value(&memory, Some(&site), &at, ty, true).unwrap());
    let bare = pointer(symbolic_storage_cell_value(&memory, None, &at, ty, true).unwrap());
    same_load(sited.address(), bare.address(), &site);
    assert_eq!(sited, bare);

    // The pointer evaluator's own producer, as a C load reaches it.
    let at = cell(1_207_034);
    let sited = pointer(symbolic_load_value(&memory, Some(&site), &at, ty).unwrap());
    let bare = pointer(symbolic_load_value(&memory, None, &at, ty).unwrap());
    same_load(sited.address(), bare.address(), &site);
    assert_eq!(sited, bare);
}

#[test]
fn a_complete_read_domain_records_its_site_and_is_the_same_domain() {
    let _session = VerificationSession::enter();
    let (_, site) = site();
    let memory = site.shared_memory().clone();
    let ty = ProgramType::Int32Pointer;
    let at = cell(1_207_041);
    let value = Address::symbolic(Variable(1_207_042));
    let sited = Pointer::from_read_at(value.clone(), ty, &memory, Some(&site), &at);
    let bare = Pointer::from_read(value, ty, &memory, &at);
    same_load(sited.provenance(), bare.provenance(), &site);
    assert_eq!(sited, bare);
}

#[test]
fn the_pointer_word_bridge_records_its_site_and_is_the_same_read() {
    let _session = VerificationSession::enter();
    let (_, site) = site();
    let memory = site.shared_memory().clone();
    let at = cell(1_207_051);
    let sited = crate::kernel::legacy_pointer_word_read(&memory, Some(&site), &at);
    let MachineTerm::MemoryLoad(point, _, _) = &sited else {
        panic!("a memory read: {sited:?}");
    };
    assert!(point.read_site().is_some_and(|path| path.id() == site.id()));
    assert_eq!(
        sited,
        crate::kernel::legacy_pointer_word_read(&memory, None, &at)
    );
}

fn load_of(address: &Address) -> crate::kernel::Load {
    address
        .as_loaded_value()
        .unwrap_or_else(|| panic!("a load: {address:?}"))
        .identity
}

fn hash_of(load: &crate::kernel::Load) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    load.hash(&mut hasher);
    hasher.finish()
}

/// A load first built from a bare memory takes the read site of the first
/// later construction that has one (`design/loads.md`, step 6), and every
/// term holding it reports that site. A still later site does not replace
/// it, and the first point stays as it was built.
#[test]
fn a_load_built_without_a_site_takes_a_later_constructions_site() {
    let _session = VerificationSession::enter();
    let (symbolic, site) = site();
    let memory = site.shared_memory().clone();
    let at = cell(1_207_061);
    let bare = Address::loaded_value(&memory, &at);
    assert!(load_of(&bare).read_site().is_none());
    assert!(!records(&bare, &site));

    let sited = Address::loaded_value_read_at(&memory, Some(&site), &at);
    assert!(
        load_of(&sited)
            .read_site()
            .is_some_and(|path| path.id() == site.id())
    );
    assert!(records(&bare, &site), "the earlier term reports the site");
    assert!(load_of(&bare).point().read_site().is_none());
    same_load(&sited, &bare, &site);

    let later = ProgramPoint::starting_at(&symbolic);
    assert_ne!(later.id(), site.id());
    let again = Address::loaded_value_read_at(&memory, Some(&later), &at);
    assert!(records(&again, &site), "the first site is kept");
}

/// Filling the slot changes no identity: the load built without a site and
/// the one built with it are one load, with one id and hash, in the same
/// order against another load before and after.
#[test]
fn a_load_given_a_later_site_is_the_same_load() {
    let _session = VerificationSession::enter();
    let (_, site) = site();
    let memory = site.shared_memory().clone();
    let at = cell(1_207_071);
    let other = load_of(&Address::loaded_value(&memory, &cell(1_207_072)));
    let bare = load_of(&Address::loaded_value(&memory, &at));
    let (id, hash, order) = (bare.id(), hash_of(&bare), bare.cmp(&other));

    let sited = load_of(&Address::loaded_value_read_at(&memory, Some(&site), &at));
    assert!(bare.read_site().is_some());
    assert_eq!(sited, bare);
    assert_eq!(sited.id(), id);
    assert_eq!(bare.id(), id);
    assert_eq!(hash_of(&sited), hash);
    assert_eq!(hash_of(&bare), hash);
    assert_eq!(sited.cmp(&bare), std::cmp::Ordering::Equal);
    assert_eq!(sited.cmp(&other), order);
    assert_eq!(bare.cmp(&other), order);
    let point = sited.point_at_read_site();
    assert!(point.read_site().is_some_and(|path| path.id() == site.id()));
    assert_eq!(&point, bare.point());
}
