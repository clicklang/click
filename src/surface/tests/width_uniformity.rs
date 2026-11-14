//! Width uniformity of the machine-integer lemma families.
//!
//! `library/integer.click` states its comparison, order, bound, in-range
//! identity, increment, predecessor and definedness lemmas per width. The
//! maintainer decided (2026-11-09) against a generic `T: intn` library
//! mechanism: the kernel rules are stated once over a format
//! (`src/kernel/machine_integer/`, checked by `matrix_tests.rs`), and this
//! fixture checks that they reach every format a sidecar can write. Each
//! family's statement is generated at every format in
//! [`machine_integer::FORMATS`] and proved by the omitted proof (`solve`),
//! with no `import click::integer`, so no library lemma is in scope.
//!
//! Each family/format pair is proved or excluded. An excluded statement does
//! not apply there ([`Exclusion`]), for example a signed-only law, which is
//! false at an unsigned format, or a 128-bit operation, which has no node to
//! lower to.
//!
//! The gate proves every remaining pair, one test per format; a format added
//! to `FORMATS` fails `every_format_is_tested_and_family_names_are_unique`
//! until it has a test here. The byte-packing laws (`uint32_pack_uint16_*`,
//! `uint32_from_le_bytes`) state a field layout of particular widths, and
//! division and remainder by a symbolic divisor have no kernel rule (they stay
//! kernel standard theorems), so neither is a family here. Nor is the wrapping
//! difference order `(0 - v) + (b - 1) < (0 - v) + b` under `v < b`: the
//! library states it as the axiom
//! `integer::uint32_difference_decreases_after_increment`. See
//! `docs/internals/testing.md`, "Width-uniformity fixture".

use crate::kernel::MachineIntegerType as Ty;
use crate::kernel::machine_integer::{self, range::range, representation};
use num_bigint::BigInt;
use num_traits::Signed;

/// One format's spelling: its type name and inclusive range.
struct Format {
    ty: Ty,
    name: &'static str,
    min: BigInt,
    max: BigInt,
}

impl Format {
    fn new(ty: Ty) -> Self {
        let name = match ty {
            Ty::Int8 => "int8",
            Ty::UInt8 => "uint8",
            Ty::Int16 => "int16",
            Ty::UInt16 => "uint16",
            Ty::Int32 => "int32",
            Ty::UInt32 => "uint32",
            Ty::Int64 => "int64",
            Ty::UInt64 => "uint64",
            Ty::Int128 => "int128",
            Ty::UInt128 => "uint128",
        };
        let (min, max) = range(ty);
        Self { ty, name, min, max }
    }

    fn signed(&self) -> bool {
        self.min.is_negative()
    }
}

/// Why a family does not apply at a format.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Exclusion {
    /// The format has no ring operations to lower to: 128 bits
    /// (`representation::word_bits`, `OPERATION_GAPS` in `matrix_tests.rs`).
    NoOperations,
    /// A signed-only law: at an unsigned format the operation wraps and the
    /// statement is false (`0 - 1` is the maximum).
    UnsignedFormat,
    /// An unsigned-only law: at a signed format the operation can overflow
    /// and the statement is false (`127 - (-128)`).
    SignedFormat,
    /// Surface `defined(...)` is about undefined behavior, which C has only
    /// for `int32` and `int64` arithmetic (`representation::files_definedness`):
    /// narrow operands are promoted, unsigned arithmetic wraps, and 128-bit
    /// values have no arithmetic.
    NoDefinedness,
}

/// Where a family applies.
#[derive(Clone, Copy)]
enum Applies {
    Everywhere,
    WithOperations,
    SignedWithOperations,
    UnsignedWithOperations,
    WhereDefinednessIsFiled,
}

impl Applies {
    fn exclusion(self, format: &Format) -> Option<Exclusion> {
        let operations = representation::word_bits(format.ty).is_some();
        match self {
            Self::Everywhere => None,
            Self::WhereDefinednessIsFiled => {
                (!representation::files_definedness(format.ty)).then_some(Exclusion::NoDefinedness)
            }
            _ if !operations => Some(Exclusion::NoOperations),
            Self::WithOperations => None,
            Self::SignedWithOperations => (!format.signed()).then_some(Exclusion::UnsignedFormat),
            Self::UnsignedWithOperations => format.signed().then_some(Exclusion::SignedFormat),
        }
    }
}

/// One width-lemma family: its statement at a format, as the text after the
/// theorem's name.
struct Family {
    name: &'static str,
    applies: Applies,
    statement: fn(&Format) -> String,
}

fn integer(value: &BigInt) -> String {
    value.to_string()
}

/// The Integer-range premises of an operation's exact value `exact`, at the
/// bounds the operands' types do not already imply.
fn range_premises(format: &Format, exact: &str, lower: bool, upper: bool) -> String {
    let mut premises = String::new();
    if lower {
        premises += &format!("    requires {} <= {exact};\n", integer(&format.min));
    }
    if upper {
        premises += &format!("    requires {exact} <= {};\n", integer(&format.max));
    }
    premises
}

const SUM: &str = "to_integer(a) + to_integer(b)";
const DIFFERENCE: &str = "to_integer(a) - to_integer(b)";
const PRODUCT: &str = "to_integer(a) * to_integer(b)";

fn two(format: &Format, body: &str) -> String {
    let t = format.name;
    format!("(a: {t}, b: {t}) {{\n{body}}}")
}

fn three(format: &Format, body: &str) -> String {
    let t = format.name;
    format!("(a: {t}, b: {t}, c: {t}) {{\n{body}}}")
}

fn identity(format: &Format, operator: &str, exact: &str, lower: bool, upper: bool) -> String {
    let t = format.name;
    let premises = range_premises(format, exact, lower, upper);
    two(
        format,
        &format!(
            "{premises}    let r: {t} = a {operator} b;\n    ensures to_integer(r) == {exact};\n"
        ),
    )
}

fn defined_by_bounds(format: &Format, operator: &str, exact: &str) -> String {
    let premises = range_premises(format, exact, true, true);
    two(
        format,
        &format!("{premises}    ensures defined(a {operator} b);\n"),
    )
}

fn defined_identity(format: &Format, operator: &str, exact: &str) -> String {
    two(
        format,
        &format!(
            "    requires defined(a {operator} b);\n    ensures to_integer(a {operator} b) == {exact};\n"
        ),
    )
}

const FAMILIES: &[Family] = &[
    // Comparison bridges: a native comparison and its exact observations.
    Family {
        name: "less_equal_to_integer",
        applies: Applies::Everywhere,
        statement: |f| {
            two(
                f,
                "    requires a <= b;\n    ensures to_integer(a) <= to_integer(b);\n",
            )
        },
    },
    Family {
        name: "less_than_to_integer",
        applies: Applies::Everywhere,
        statement: |f| {
            two(
                f,
                "    requires a < b;\n    ensures to_integer(a) < to_integer(b);\n",
            )
        },
    },
    Family {
        name: "greater_equal_to_integer",
        applies: Applies::Everywhere,
        statement: |f| {
            two(
                f,
                "    requires a >= b;\n    ensures to_integer(a) >= to_integer(b);\n",
            )
        },
    },
    Family {
        name: "to_integer_less_equal_implies_less_equal",
        applies: Applies::Everywhere,
        statement: |f| {
            two(
                f,
                "    requires to_integer(a) <= to_integer(b);\n    ensures a <= b;\n",
            )
        },
    },
    Family {
        name: "to_integer_less_than_implies_less_than",
        applies: Applies::Everywhere,
        statement: |f| {
            two(
                f,
                "    requires to_integer(a) < to_integer(b);\n    ensures a < b;\n",
            )
        },
    },
    Family {
        name: "to_integer_equal_implies_equal",
        applies: Applies::Everywhere,
        statement: |f| {
            two(
                f,
                "    requires to_integer(a) == to_integer(b);\n    ensures a == b;\n",
            )
        },
    },
    // Order: transitivity and its relatives.
    Family {
        name: "less_equal_transitive",
        applies: Applies::Everywhere,
        statement: |f| {
            three(
                f,
                "    requires a <= b;\n    requires b <= c;\n    ensures a <= c;\n",
            )
        },
    },
    Family {
        name: "less_than_transitive",
        applies: Applies::Everywhere,
        statement: |f| {
            three(
                f,
                "    requires a < b;\n    requires b < c;\n    ensures a < c;\n",
            )
        },
    },
    Family {
        name: "less_equal_less_than_transitive",
        applies: Applies::Everywhere,
        statement: |f| {
            three(
                f,
                "    requires a <= b;\n    requires b < c;\n    ensures a < c;\n",
            )
        },
    },
    Family {
        name: "less_than_less_equal_transitive",
        applies: Applies::Everywhere,
        statement: |f| {
            three(
                f,
                "    requires a < b;\n    requires b <= c;\n    ensures a < c;\n",
            )
        },
    },
    Family {
        name: "greater_equal_transitive",
        applies: Applies::Everywhere,
        statement: |f| {
            three(
                f,
                "    requires a >= b;\n    requires b >= c;\n    ensures a >= c;\n",
            )
        },
    },
    Family {
        name: "less_than_implies_less_equal",
        applies: Applies::Everywhere,
        statement: |f| two(f, "    requires a < b;\n    ensures a <= b;\n"),
    },
    Family {
        name: "less_than_implies_not_greater_equal",
        applies: Applies::Everywhere,
        statement: |f| two(f, "    requires a < b;\n    ensures not (a >= b);\n"),
    },
    Family {
        name: "greater_equal_implies_reversed_less_equal",
        applies: Applies::Everywhere,
        statement: |f| two(f, "    requires a >= b;\n    ensures b <= a;\n"),
    },
    Family {
        name: "less_equal_and_not_less_than_implies_equal",
        applies: Applies::Everywhere,
        statement: |f| {
            two(
                f,
                "    requires a <= b;\n    requires not (a < b);\n    ensures a == b;\n",
            )
        },
    },
    Family {
        name: "less_equal_and_not_equal_implies_less_than",
        applies: Applies::Everywhere,
        statement: |f| {
            two(
                f,
                "    requires a <= b;\n    requires a != b;\n    ensures a < b;\n",
            )
        },
    },
    Family {
        name: "positive_is_nonnegative",
        applies: Applies::Everywhere,
        statement: |f| {
            format!(
                "(v: {}) {{\n    requires 0 < v;\n    ensures 0 <= v;\n}}",
                f.name
            )
        },
    },
    // Range of an observation.
    Family {
        name: "to_integer_bounds",
        applies: Applies::Everywhere,
        statement: |f| {
            format!(
                "(v: {}) {{\n    ensures {} <= to_integer(v);\n    ensures to_integer(v) <= {};\n}}",
                f.name,
                integer(&f.min),
                integer(&f.max)
            )
        },
    },
    Family {
        name: "round_trip",
        applies: Applies::Everywhere,
        statement: |f| {
            format!(
                "(z: Integer) {{\n    requires {} <= z;\n    requires z <= {};\n    ensures to_integer(to_{}(z)) == z;\n}}",
                integer(&f.min),
                integer(&f.max),
                f.name
            )
        },
    },
    // In-range observation identities, with Integer-range premises (never
    // `defined`, which C files only at `int32` and `int64`). `let r: T`
    // makes the operation native at its format; inside `to_integer(...)` an
    // 8- or 16-bit sum is C's promoted `int32` sum.
    Family {
        name: "add_to_integer",
        applies: Applies::WithOperations,
        statement: |f| identity(f, "+", SUM, f.signed(), true),
    },
    Family {
        name: "subtract_to_integer",
        applies: Applies::WithOperations,
        statement: |f| identity(f, "-", DIFFERENCE, true, f.signed()),
    },
    Family {
        name: "multiply_to_integer",
        applies: Applies::WithOperations,
        statement: |f| identity(f, "*", PRODUCT, f.signed(), true),
    },
    // Increment and predecessor forms.
    Family {
        name: "increment_upper_bound",
        applies: Applies::WithOperations,
        statement: |f| {
            let t = f.name;
            format!(
                "(v: {t}, u: {t}) {{\n    requires v < u;\n    let n: {t} = v + 1;\n    ensures to_integer(n) <= to_integer(u);\n}}"
            )
        },
    },
    Family {
        name: "increment_strictly_increases",
        applies: Applies::WithOperations,
        statement: |f| {
            let t = f.name;
            format!(
                "(v: {t}, u: {t}) {{\n    requires v < u;\n    let n: {t} = v + 1;\n    ensures to_integer(v) < to_integer(n);\n}}"
            )
        },
    },
    Family {
        name: "increment_lower_bound",
        applies: Applies::WithOperations,
        statement: |f| {
            let t = f.name;
            format!(
                "(v: {t}, l: {t}, u: {t}) {{\n    requires l <= v;\n    requires v < u;\n    let n: {t} = v + 1;\n    ensures to_integer(l) <= to_integer(n);\n}}"
            )
        },
    },
    Family {
        name: "positive_predecessor_is_nonnegative",
        applies: Applies::WithOperations,
        statement: |f| {
            let t = f.name;
            format!(
                "(v: {t}) {{\n    requires 0 < v;\n    let p: {t} = v - 1;\n    ensures 0 <= to_integer(p);\n}}"
            )
        },
    },
    Family {
        name: "positive_predecessor_strictly_decreases",
        applies: Applies::WithOperations,
        statement: |f| {
            let t = f.name;
            format!(
                "(v: {t}) {{\n    requires 0 < v;\n    let p: {t} = v - 1;\n    ensures to_integer(p) < to_integer(v);\n}}"
            )
        },
    },
    Family {
        name: "nonnegative_predecessor_upper_bound",
        applies: Applies::SignedWithOperations,
        statement: |f| {
            let t = f.name;
            format!(
                "(v: {t}, b: {t}) {{\n    requires 0 <= v;\n    requires v <= b;\n    let p: {t} = v - 1;\n    ensures to_integer(p) <= to_integer(b);\n}}"
            )
        },
    },
    Family {
        name: "less_than_implies_positive_difference",
        applies: Applies::UnsignedWithOperations,
        statement: |f| {
            let t = f.name;
            format!(
                "(v: {t}, u: {t}) {{\n    requires v < u;\n    let d: {t} = u - v;\n    ensures 0 < to_integer(d);\n}}"
            )
        },
    },
    // Definedness forms, where C files definedness.
    Family {
        name: "add_defined_by_integer_bounds",
        applies: Applies::WhereDefinednessIsFiled,
        statement: |f| defined_by_bounds(f, "+", SUM),
    },
    Family {
        name: "subtract_defined_by_integer_bounds",
        applies: Applies::WhereDefinednessIsFiled,
        statement: |f| defined_by_bounds(f, "-", DIFFERENCE),
    },
    Family {
        name: "multiply_defined_by_integer_bounds",
        applies: Applies::WhereDefinednessIsFiled,
        statement: |f| defined_by_bounds(f, "*", PRODUCT),
    },
    Family {
        name: "increment_below_max_is_defined",
        applies: Applies::WhereDefinednessIsFiled,
        statement: |f| {
            format!(
                "(v: {}) {{\n    requires v < {};\n    ensures defined(v + 1);\n}}",
                f.name,
                integer(&f.max)
            )
        },
    },
    Family {
        name: "nonnegative_add_within_max_is_defined",
        applies: Applies::WhereDefinednessIsFiled,
        statement: |f| {
            let t = f.name;
            let max = integer(&f.max);
            format!(
                "(v: {t}, amount: {t}) {{\n    requires 0 <= amount;\n    requires to_integer(v) <= {max} - to_integer(amount);\n    ensures defined(v + amount);\n}}"
            )
        },
    },
    Family {
        name: "nonnegative_subtract_within_value_is_defined",
        applies: Applies::WhereDefinednessIsFiled,
        statement: |f| {
            let t = f.name;
            format!(
                "(v: {t}, amount: {t}) {{\n    requires 0 <= amount;\n    requires amount <= v;\n    ensures defined(v - amount);\n}}"
            )
        },
    },
    Family {
        name: "defined_add_to_integer",
        applies: Applies::WhereDefinednessIsFiled,
        statement: |f| defined_identity(f, "+", SUM),
    },
    Family {
        name: "defined_subtract_to_integer",
        applies: Applies::WhereDefinednessIsFiled,
        statement: |f| defined_identity(f, "-", DIFFERENCE),
    },
    Family {
        name: "defined_multiply_to_integer",
        applies: Applies::WhereDefinednessIsFiled,
        statement: |f| defined_identity(f, "*", PRODUCT),
    },
];

fn theorem(family: &Family, format: &Format) -> String {
    format!(
        "theorem {}_{}{}\n",
        family.name,
        format.name,
        (family.statement)(format)
    )
}

/// The families the gate proves at every format: a comparison bridge and
/// the range, the standard-library item's intended regression. Each costs
/// about a millisecond per format after the first verification's library
/// setup (about 0.35s); the nightly per-format tests prove every family.
const GATE_FAMILIES: &[&str] = &["less_equal_to_integer", "to_integer_bounds"];

/// The theorems of `families` at `formats` that are not excluded.
fn proved_theorems<'a>(
    families: impl Iterator<Item = &'a Family> + Clone,
    formats: &[Ty],
) -> Vec<String> {
    let mut theorems = Vec::new();
    for ty in formats {
        let format = Format::new(*ty);
        for family in families.clone() {
            if family.applies.exclusion(&format).is_none() {
                theorems.push(theorem(family, &format));
            }
        }
    }
    theorems
}

/// Proves `theorems` in one source by the omitted proof.
fn prove_by_omitted_proof(label: &str, theorems: &[String]) {
    let source = theorems.join("\n");
    assert!(
        !source.contains("import") && !source.contains(" by "),
        "{source}"
    );
    let verified = crate::surface::verify_click_theorems(&source)
        .unwrap_or_else(|error| panic!("{label}: {}\n{source}", error.message()));
    assert_eq!(
        verified.len(),
        source.matches("    ensures ").count(),
        "{label}"
    );
}

#[test]
fn width_family_representatives_close_at_every_format() {
    let families = FAMILIES
        .iter()
        .filter(|family| GATE_FAMILIES.contains(&family.name));
    prove_by_omitted_proof(
        "representatives",
        &proved_theorems(families, &machine_integer::FORMATS),
    );
}

macro_rules! format_tests {
    ($($test:ident => $ty:expr),* $(,)?) => {
        $(
            #[test]
            #[ignore = "nightly: 0.4s to 1.3s each, about 6s for all ten"]
            fn $test() {
                prove_by_omitted_proof(stringify!($test), &proved_theorems(FAMILIES.iter(), &[$ty]));
            }
        )*
        const TESTED_FORMATS: &[Ty] = &[$($ty),*];
    };
}

format_tests! {
    width_families_close_at_int8 => Ty::Int8,
    width_families_close_at_uint8 => Ty::UInt8,
    width_families_close_at_int16 => Ty::Int16,
    width_families_close_at_uint16 => Ty::UInt16,
    width_families_close_at_int32 => Ty::Int32,
    width_families_close_at_uint32 => Ty::UInt32,
    width_families_close_at_int64 => Ty::Int64,
    width_families_close_at_uint64 => Ty::UInt64,
    width_families_close_at_int128 => Ty::Int128,
    width_families_close_at_uint128 => Ty::UInt128,
}

#[test]
fn every_format_is_tested_and_family_names_are_unique() {
    let mut tested = TESTED_FORMATS.to_vec();
    let mut formats = machine_integer::FORMATS.to_vec();
    tested.sort();
    formats.sort();
    assert_eq!(
        tested, formats,
        "every format in machine_integer::FORMATS needs a width_families_close_at_* test"
    );
    let mut names = std::collections::BTreeSet::new();
    for family in FAMILIES {
        assert!(
            names.insert(family.name),
            "family `{}` repeats",
            family.name
        );
    }
    for name in GATE_FAMILIES {
        assert!(names.contains(name), "gate family `{name}` is not a family");
    }
}
