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
            // The parser spreads this back into the same pointer and length.
            arguments[position] =
                format!("click::rust::slice::from_raw_parts({pointer}, {length})");
        }
    }
    arguments
}

/// The type a slice constructor is written at, `Slice<u8>` in a function
/// written in Rust syntax and `Slice<uint8>` elsewhere: a slice standing
/// alone, `Slice<u8>::Slice(p, n)[1]`, has no context to infer it from.
pub(crate) fn slice_type_spelling(element: &ProgramType) -> Option<String> {
    let name = if rust_spelling() {
        rust_scalar_spelling(element)?
    } else {
        crate::surface::printing::machine_integer_type_name(
            crate::kernel::MachineIntegerType::from_c_type(*element)?,
        )
    };
    Some(format!("Slice<{name}>"))
}

/// The subslice whose length is `slice::subslice_len(start, end, len)`, as
/// written: `bytes[a..b]`, `bytes[a..]` or `bytes[..b]`, when `len` is a
/// slice's own length.
pub(crate) fn subslice_of_length(start: &str, end: &str, len: &str) -> Option<String> {
    let slice = unparenthesized(len).strip_suffix(".len()")?;
    let start = usize_bound(start);
    let start = if start == "0" { "" } else { start.as_str() };
    let end = if unparenthesized(end) == unparenthesized(len) {
        String::new()
    } else {
        usize_bound(end)
    };
    Some(format!("{slice}[{start}..{end}]"))
}

/// The subslice a constructed slice with data `pointer` and length `length`
/// was built as, `bytes[a..b]`, `bytes[a..]` or `bytes[..b]`, for a value the
/// kernel recorded as constructed under a subslice's bounds.
pub(crate) fn subslice_spelling(pointer: &str, length: &str) -> Option<String> {
    let (pointer, length) = (unparenthesized(pointer), unparenthesized(length));
    let (base, start) = match pointer
        .strip_prefix('&')
        .and_then(|element| element.strip_suffix(']'))
        .and_then(|element| element.rsplit_once('['))
    {
        Some((base, start)) => (base, Some(start)),
        None => match pointer.split_once(" + ") {
            Some((base, start)) => (base, Some(start)),
            None => (pointer, None),
        },
    };
    let (slice, own_lengths) = slice_with_data(base)?;
    // The length a subslice was built with, `end - start`, gives back its
    // end; the slice's own length is an open end.
    let start = start.map(usize_bound);
    let end = match &start {
        Some(start) => [start.clone(), format!("{start}u64")]
            .iter()
            .find_map(|start| length.strip_suffix(&format!(" - {start}")))
            .map(unparenthesized)
            .map_or_else(
                || {
                    start
                        .parse::<u64>()
                        .ok()
                        .zip(usize_bound(length).parse::<u64>().ok())
                        .and_then(|(start, length)| start.checked_add(length))
                        .map_or_else(|| format!("{start} + {length}"), |end| end.to_string())
                },
                str::to_string,
            ),
        None => length.to_string(),
    };
    let end = (!own_lengths.contains(&end)).then(|| usize_bound(&end));
    if start.is_none() && end.is_none() {
        return Some(slice);
    }
    Some(format!(
        "{slice}[{}..{}]",
        start.unwrap_or_default(),
        end.unwrap_or_default()
    ))
}

/// The slice whose data pointer is spelled `pointer`, with the spellings of
/// its own length: a slice parameter, also at another point (`old(bytes)`),
/// or a slice value's `x.as_ptr()`.
fn slice_with_data(pointer: &str) -> Option<(String, Vec<String>)> {
    if let Some(slice) = pointer.strip_suffix(".as_ptr()") {
        return Some((slice.to_string(), vec![format!("{slice}.len()")]));
    }
    let (wrap, name): (Box<dyn Fn(&str) -> String>, &str) = match pointer
        .strip_prefix("old(")
        .and_then(|rest| rest.strip_suffix(')'))
    {
        Some(name) => (Box::new(|inner| format!("old({inner})")), name),
        None => match pointer
            .strip_prefix("at(")
            .and_then(|rest| rest.strip_suffix(')'))
            .and_then(|rest| rest.split_once(", "))
        {
            Some((point, name)) => {
                let point = point.to_string();
                (Box::new(move |inner| format!("at({point}, {inner})")), name)
            }
            None => (Box::new(|inner| inner.to_string()), pointer),
        },
    };
    if !rust_slice_parameters()?
        .iter()
        .any(|parameter| parameter == name)
    {
        return None;
    }
    // A slice parameter's length never changes, so it is also spelled
    // without the point.
    let lengths = vec![
        format!("{pointer}.len()"),
        wrap(&format!("{name}.len()")),
        wrap(&format!("{name}_len")),
        format!("{name}.len()"),
        format!("{name}_len"),
    ];
    Some((pointer.to_string(), lengths))
}

/// A subslice bound as written: `usize`, so a numeral needs no suffix.
fn usize_bound(bound: &str) -> String {
    let bound = unparenthesized(bound);
    match bound.strip_suffix("u64") {
        Some(digits) if !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()) => {
            digits.to_string()
        }
        _ => bound.to_string(),
    }
}

/// `text` without parentheses that enclose all of it.
fn unparenthesized(text: &str) -> &str {
    let Some(inner) = text
        .strip_prefix('(')
        .and_then(|rest| rest.strip_suffix(')'))
    else {
        return text;
    };
    let mut depth = 0usize;
    for character in inner.chars() {
        match character {
            '(' => depth += 1,
            ')' if depth == 0 => return text,
            ')' => depth -= 1,
            _ => {}
        }
    }
    if depth == 0 { inner } else { text }
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
pub(super) fn rust_scalar_spelling(c_type: &ProgramType) -> Option<&'static str> {
    Some(match c_type {
        ProgramType::Int8 => "i8",
        ProgramType::Int16 => "i16",
        ProgramType::Int32 => "i32",
        ProgramType::UInt8 => "u8",
        ProgramType::UInt16 => "u16",
        ProgramType::UInt32 => "u32",
        ProgramType::Int64 => "i64",
        ProgramType::UInt64 => "u64",
        ProgramType::Int128 => "i128",
        ProgramType::UInt128 => "u128",
        _ => return None,
    })
}

/// A call of the library's slice functions, or its slice constructor, in
/// the Rust spelling: `x.len()`, `x.as_ptr()`, and
/// `slice::from_raw_parts(p, n)`. `name` may carry the qualified path and
/// an instance, `click::rust::slice::len::<uint8>`.
pub(crate) fn slice_call_spelling(name: &str, arguments: &[String]) -> Option<String> {
    // Only a function written in Rust syntax reads Rust's slice methods
    // back; elsewhere the library call is its own spelling.
    if !rust_spelling() {
        return None;
    }
    let base = name.split("::<").next().unwrap_or(name);
    let method = base
        .strip_prefix("click::rust::slice::")
        .or_else(|| base.strip_prefix("slice::"))?;
    match (method, arguments) {
        ("len", [slice]) => Some(format!("{slice}.len()")),
        ("as_ptr", [slice]) => Some(format!("{slice}.as_ptr()")),
        // A call is spelled as the call it is; its slice is a constructor
        // only once unfolded.
        ("from_raw_parts", [pointer, length]) => Some(format!(
            "click::rust::slice::from_raw_parts({pointer}, {length})"
        )),
        // A subslice's length is that subslice's `.len()`: written as
        // `end - start` it would read as Integer subtraction in a comparison.
        ("subslice_len", [start, end, len]) => {
            subslice_of_length(start, end, len).map(|subslice| format!("{subslice}.len()"))
        }
        _ => None,
    }
}
