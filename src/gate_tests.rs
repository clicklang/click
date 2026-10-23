//! API and corpus checks in the fast gate's single test executable.
//! Executable/installation checks are compiled only by the production nightly.

// Shared fixtures retain helpers used only by their standalone nightly targets.
#![allow(dead_code)]
// Each standalone nightly fixture keeps its own support-module namespace.
#![allow(clippy::duplicate_mod)]

#[path = "../tests/condition_transport_api.rs"]
mod condition_transport_api;

#[path = "../tests/documentation.rs"]
mod documentation;

#[path = "../tests/mdtests.rs"]
mod mdtests;

#[path = "../tests/examples.rs"]
// Its crate-level recursion limit still applies to the standalone target.
#[allow(unused_attributes)]
mod examples;

#[path = "../tests/compiler_import.rs"]
mod compiler_import;

#[path = "../tests/cpp_import.rs"]
mod cpp_import;

#[path = "../tests/bitcoin_core_money_range.rs"]
mod bitcoin_core_money_range;

#[path = "../tests/libcxx_span.rs"]
mod libcxx_span;

#[path = "../tests/libcxx_functional.rs"]
mod libcxx_functional;

#[path = "../tests/rust_import.rs"]
mod rust_import;
