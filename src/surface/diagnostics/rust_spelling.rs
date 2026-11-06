//! How diagnostics print the places of a function whose sidecar signature is
//! written in Rust syntax.

use super::*;

thread_local! {
    /// The slice parameters of the function being checked when its
    /// signature is written in Rust syntax; `None` for the C-shaped spelling.
    static RUST_SPELLING: std::cell::RefCell<Option<std::rc::Rc<[String]>>> =
        const { std::cell::RefCell::new(None) };
    /// The iterator each loop of that function advances.
    static RUST_LOOP_ITERATORS: std::cell::RefCell<
        std::sync::Arc<[Option<crate::languages::c::syntax::RustLoopIterator>]>,
    > = std::cell::RefCell::new(std::sync::Arc::from([]));
    /// The loop whose phases are being checked, whose iterator a proof
    /// there names bare `iter`.
    static CURRENT_LOOP: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
    /// For each pure function that takes a slice, the positions in its
    /// lowered arguments where a slice's pointer is, its length following.
    static PURE_FUNCTION_SLICES: std::cell::RefCell<
        std::collections::BTreeMap<String, std::rc::Rc<[usize]>>,
    > = const { std::cell::RefCell::new(std::collections::BTreeMap::new()) };
}

/// Records that the pure function `name` takes slices at the written
/// parameter positions `written`, so a call prints each slice as one
/// argument, as it is written.
pub(crate) fn record_pure_function_slices(name: &str, written: &[usize]) {
    let lowered: std::rc::Rc<[usize]> = written
        .iter()
        .enumerate()
        .map(|(before, position)| position + before)
        .collect();
    PURE_FUNCTION_SLICES.with(|slot| {
        slot.borrow_mut().insert(name.to_string(), lowered);
    });
}

/// The spelled arguments of a call to the pure function `name`, with each
/// slice, lowered as its pointer and its length, written as one argument
/// again: the parameter it is (`bytes`, `old(bytes)`), or
/// `slice::from_raw_parts(p, n)` for another pointer and length.
pub(crate) fn slice_call_arguments(name: &str, mut arguments: Vec<String>) -> Vec<String> {
    let Some(slices) = PURE_FUNCTION_SLICES.with(|slot| slot.borrow().get(name).cloned()) else {
        return arguments;
    };
    if !slices.iter().all(|position| position + 1 < arguments.len()) {
        return arguments;
    }
    for &position in slices.iter().rev() {
        let length = arguments.remove(position + 1);
        let pointer = &arguments[position];
        let parameter = pointer
            .strip_prefix("old(")
            .or_else(|| {
                pointer
                    .strip_prefix("at(")
                    .and_then(|rest| rest.split_once(", ").map(|(_, inner)| inner))
            })
            .and_then(|inner| inner.strip_suffix(')'))
            .unwrap_or(pointer);
        let own_length = [format!("{parameter}.len()"), format!("{parameter}_len")];
        if !own_length.contains(&length) {
            arguments[position] = format!("slice::from_raw_parts({pointer}, {length})");
        }
    }
    arguments
}

/// While it lives, loop `index`'s phases are being checked: its iterator's
/// state is printed `iter.len()`, every other loop's `loop(i).iter.len()`.
pub(crate) struct LoopPhaseSpelling(Option<usize>);

impl LoopPhaseSpelling {
    pub(crate) fn enter(index: usize) -> Self {
        Self(CURRENT_LOOP.with(|slot| slot.replace(Some(index))))
    }
}

impl Drop for LoopPhaseSpelling {
    fn drop(&mut self) {
        CURRENT_LOOP.with(|slot| slot.set(self.0));
    }
}

/// Prints the places of a function whose signature is written in Rust
/// syntax as its sidecar writes them: a slice's length `bytes.len()`, a cast
/// `(value as u32)`, and a field through a reference `p.field`. Like the
/// ambient naming, it stays set after the function's check, for a failure
/// rendered later; the next declaration replaces it. The parser reads each
/// form back in such a function, so `click expand` prints through it too.
pub(crate) fn enter_rust_spelling(signature: Option<&super::FunctionSignature>) {
    let spelling = signature
        .and_then(super::FunctionSignature::rust_slice_parameters)
        .map(std::rc::Rc::<[String]>::from);
    RUST_SPELLING.with(|slot| *slot.borrow_mut() = spelling);
    let iterators = signature
        .map(|signature| signature.rust_loop_iterators().clone())
        .unwrap_or_else(|| std::sync::Arc::from([]));
    RUST_LOOP_ITERATORS.with(|slot| *slot.borrow_mut() = iterators);
}

/// The slice parameters of the function whose places are printed, when its
/// signature is written in Rust syntax: an expansion's own function, else
/// the function last checked.
pub(super) fn rust_slice_parameters() -> Option<std::rc::Rc<[String]>> {
    REFERENCE_CARRIERS
        .with(|scopes| {
            scopes
                .borrow()
                .iter()
                .rev()
                .find_map(|scope| scope.rust_spelling.clone())
        })
        .unwrap_or_else(|| RUST_SPELLING.with(|slot| slot.borrow().clone()))
}

pub(crate) fn rust_spelling() -> bool {
    rust_slice_parameters().is_some()
}

/// The spelling of the program variable `name` where its bare name is not
/// its own: `bytes.len()` for the length of the Rust slice parameter `bytes`,
/// and `c(iterations)`, or `rust(iterations)`, for a variable named like a
/// loop's pass count, which that spelling means wherever it is written.
pub(crate) fn rust_variable_spelling(name: &str) -> Option<String> {
    if name == crate::surface::LOOP_ITERATIONS_NAME {
        return Some(if rust_spelling() {
            format!("rust({name})")
        } else {
            format!("c({name})")
        });
    }
    if let Some(spelling) = RUST_LOOP_ITERATORS.with(|slot| {
        crate::surface::rust_iterator_spelling(
            &slot.borrow(),
            CURRENT_LOOP.with(std::cell::Cell::get),
            name,
        )
    }) {
        return Some(spelling);
    }
    let slice = name.strip_suffix("_len")?;
    rust_slice_parameters()?
        .iter()
        .any(|known| known == slice)
        .then(|| format!("{slice}.len()"))
}

/// The Rust name of the scalar type `c_type`, `u32` for `uint32`.
pub(super) fn rust_scalar_spelling(c_type: &CType) -> Option<&'static str> {
    Some(match c_type {
        CType::Int8 => "i8",
        CType::Int16 => "i16",
        CType::Int32 => "i32",
        CType::UInt8 => "u8",
        CType::UInt16 => "u16",
        CType::UInt32 => "u32",
        CType::Int64 => "i64",
        CType::UInt64 => "u64",
        CType::Int128 => "i128",
        CType::UInt128 => "u128",
        _ => return None,
    })
}

/// A call of the library's slice functions, or its slice constructor, in
/// the Rust spelling: `x.len()`, `x.as_ptr()`, and
/// `slice::from_raw_parts(p, n)`. `name` may carry the qualified path and
/// an instance, `click::rust::slice::len::<uint8>`.
pub(crate) fn slice_call_spelling(name: &str, arguments: &[String]) -> Option<String> {
    let base = name.split("::<").next().unwrap_or(name);
    let method = base
        .strip_prefix("click::rust::slice::")
        .or_else(|| base.strip_prefix("slice::"))?;
    match (method, arguments) {
        ("len", [slice]) => Some(format!("{slice}.len()")),
        ("as_ptr", [slice]) => Some(format!("{slice}.as_ptr()")),
        ("from_raw_parts", [pointer, length]) => {
            Some(format!("slice::from_raw_parts({pointer}, {length})"))
        }
        _ => None,
    }
}
