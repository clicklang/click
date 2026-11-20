//! The C program-language frontend and source model.

pub(crate) mod address_taken;
pub mod compiler_import;
pub(crate) mod formatted_output;
pub(crate) mod integer_specifiers;
pub(crate) mod option_profile;
pub(crate) mod projection;
pub mod source;
pub(crate) mod source_map;
pub mod syntax;
pub(crate) mod system_headers;
pub mod target;
pub mod thread_runtime;
pub(crate) mod variadic;

#[cfg(test)]
mod linux_rbtree_tests;
#[cfg(test)]
mod tests;
