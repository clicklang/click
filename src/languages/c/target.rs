//! Concrete implementation choices for the supported C subset.
//!
//! These are target assumptions, not properties of ISO C or LP64 in general.
//! The Linux kernel builds with `-funsigned-char`, so its plain `char` is
//! unsigned; x86-64 user space follows the System V ABI, where plain `char`
//! is signed. We model both targets' x86-64 data layout. This does not claim
//! support for every kernel compiler option, extension, or execution
//! behavior.

use super::syntax::{C0Type, CAbi};
use crate::kernel::ByteOrder;

/// The signedness a target gives plain `char`.
///
/// Plain `char` stays a type of its own in C compatibility, distinct from
/// both `signed char` and `unsigned char` (C11 6.2.5p15), so the C frontend
/// carries this choice inside its `char` types rather than resolving `char`
/// to one of the other two. Only its values and its kernel representation
/// follow [`PlainChar::byte_type`].
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum PlainChar {
    Unsigned,
    Signed,
}

impl PlainChar {
    /// The character type whose range and representation plain `char` has:
    /// `unsigned char` (`uint8`) or `signed char` (`int8`).
    pub const fn byte_type(self) -> C0Type {
        match self {
            Self::Unsigned => C0Type::UInt8,
            Self::Signed => C0Type::Int8,
        }
    }

    pub const fn is_signed(self) -> bool {
        matches!(self, Self::Signed)
    }

    /// `CHAR_MIN` and `CHAR_MAX`.
    pub const fn range(self) -> (i64, i64) {
        match self {
            Self::Unsigned => (0, u8::MAX as i64),
            Self::Signed => (i8::MIN as i64, i8::MAX as i64),
        }
    }

    /// The value of a character constant whose execution character is the
    /// byte `byte`: C11 6.4.4.4p10 converts the byte to plain `char` first,
    /// so a byte of 0x80 or more is negative where plain `char` is signed.
    pub const fn character_value(self, byte: u8) -> i64 {
        match self {
            Self::Unsigned => byte as i64,
            Self::Signed => byte as i8 as i64,
        }
    }
}

/// The integer conversion rank of a 64-bit LP64 integer type. `long` and
/// `long long` have the same size and representation on every supported
/// target, but they are distinct, incompatible C types, as GCC and Clang
/// treat them: `long *` and `long long *` do not convert implicitly, and
/// declarations that differ only in rank conflict.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum LongRank {
    Long,
    LongLong,
}

impl LongRank {
    /// The C spelling of the signed type of this rank.
    pub const fn signed_spelling(self) -> &'static str {
        match self {
            Self::Long => "long",
            Self::LongLong => "long long",
        }
    }

    /// The C spelling of the unsigned type of this rank.
    pub const fn unsigned_spelling(self) -> &'static str {
        match self {
            Self::Long => "unsigned long",
            Self::LongLong => "unsigned long long",
        }
    }

    /// C11 6.3.1.8: of two 64-bit operands, the one of greater rank
    /// determines the common type.
    pub const fn max(self, other: Self) -> Self {
        match (self, other) {
            (Self::LongLong, _) | (_, Self::LongLong) => Self::LongLong,
            _ => Self::Long,
        }
    }
}

/// The optimization level a project's C units are verified for: the one
/// level a project names, `-O2` by default
/// (`docs/reference/cli/import.md#optimization-level`). Click's checks cover the assumptions GCC's optimizer makes
/// at `-O2`, so a verified claim holds for the optimized build.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash)]
pub enum COptimization {
    O0,
    #[default]
    O2,
}

impl COptimization {
    pub const ALL: &'static [Self] = &[Self::O0, Self::O2];

    /// The compiler flag, which is also the project file's spelling.
    pub const fn flag(self) -> &'static str {
        match self {
            Self::O0 => "-O0",
            Self::O2 => "-O2",
        }
    }

    /// Resolves a project file's `optimization`; omitted, it is `-O2`.
    pub fn from_setting(setting: Option<&str>) -> Result<Self, String> {
        let Some(setting) = setting else {
            return Ok(Self::default());
        };
        Self::ALL
            .iter()
            .copied()
            .find(|level| level.flag() == setting)
            .ok_or_else(|| {
                format!(
                    "unknown optimization level `{setting}`; accepted levels are {}",
                    Self::ALL
                        .iter()
                        .map(|level| format!("`{}`", level.flag()))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })
    }

    /// Whether GCC optimizes at this level, and so acts on the attributes
    /// it trusts as programmer promises.
    pub const fn optimizes(self) -> bool {
        !matches!(self, Self::O0)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum CTarget {
    X86_64LinuxKernel,
    /// C11/POSIX user space under the x86-64 System V ABI: the same LP64
    /// layout, but plain `char` is signed, as GCC and Clang build it by
    /// default, and there is no `__KERNEL__` predefine.
    X86_64LinuxUserspace,
}

impl CTarget {
    pub const SUPPORTED: Self = Self::X86_64LinuxUserspace;

    /// The target triple every selectable target shares; the mode tells
    /// kernel and user space apart.
    pub const TRIPLE: &'static str = "x86_64-unknown-linux-gnu";

    /// Every selectable target, in the order a diagnostic lists them.
    pub const ALL: &'static [Self] = &[Self::X86_64LinuxKernel, Self::X86_64LinuxUserspace];

    /// The mode spelling: `kernel` or `userspace`.
    pub const fn mode(self) -> &'static str {
        match self {
            Self::X86_64LinuxKernel => "kernel",
            Self::X86_64LinuxUserspace => "userspace",
        }
    }

    /// The target and mode, as diagnostics and lock identities name them.
    pub const fn name(self) -> &'static str {
        match self {
            Self::X86_64LinuxKernel => "x86_64-unknown-linux-gnu (kernel)",
            Self::X86_64LinuxUserspace => "x86_64-unknown-linux-gnu (userspace)",
        }
    }

    /// Resolves a `target` and `mode` pair, as a project file or a sidecar
    /// spells them. An omitted target is the shared triple and an omitted
    /// mode is user space. A retired single-name spelling is
    /// refused with its replacement.
    pub fn from_parts(target: Option<&str>, mode: Option<&str>) -> Result<Self, String> {
        if let Some(target) = target
            && target != Self::TRIPLE
        {
            return Err(
                match Self::ALL
                    .iter()
                    .find(|known| known.retired_name() == target)
                {
                    Some(Self::X86_64LinuxKernel) => format!(
                        "C target `{target}` is retired; use target `{}` with mode `kernel`",
                        Self::TRIPLE
                    ),
                    Some(Self::X86_64LinuxUserspace) => format!(
                        "C target `{target}` is retired; use target `{}`, whose default mode is `userspace`",
                        Self::TRIPLE
                    ),
                    None => format!(
                        "unknown C target `{target}`; the accepted target is `{}`",
                        Self::TRIPLE
                    ),
                },
            );
        }
        match mode {
            None => Ok(Self::SUPPORTED),
            Some(name) => Self::ALL
                .iter()
                .copied()
                .find(|known| known.mode() == name)
                .ok_or_else(|| {
                    format!(
                        "unknown C mode `{name}`; accepted modes are {}",
                        Self::ALL
                            .iter()
                            .map(|known| format!("`{}`", known.mode()))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }),
        }
    }

    /// The single-name spelling this target had before targets were
    /// spelled as a triple and a mode.
    const fn retired_name(self) -> &'static str {
        match self {
            Self::X86_64LinuxKernel => "x86_64-linux-kernel",
            Self::X86_64LinuxUserspace => "x86_64-linux-userspace",
        }
    }

    pub const fn abi(self) -> CAbi {
        match self {
            Self::X86_64LinuxKernel | Self::X86_64LinuxUserspace => CAbi::Lp64,
        }
    }

    pub const fn char_bits(self) -> u32 {
        match self {
            Self::X86_64LinuxKernel | Self::X86_64LinuxUserspace => 8,
        }
    }

    /// The order the kernel's byte view of integer cells follows. Both
    /// selectable targets are x86-64, which is little-endian, matching the
    /// `__BYTE_ORDER__` predefine below.
    pub const fn byte_order(self) -> ByteOrder {
        match self {
            Self::X86_64LinuxKernel | Self::X86_64LinuxUserspace => ByteOrder::Little,
        }
    }

    /// The signedness of plain `char`: unsigned for the kernel, which builds
    /// with `-funsigned-char`, and signed for user space, as the x86-64
    /// System V ABI specifies.
    pub const fn plain_char(self) -> PlainChar {
        match self {
            Self::X86_64LinuxKernel => PlainChar::Unsigned,
            Self::X86_64LinuxUserspace => PlainChar::Signed,
        }
    }

    /// The rank of `int64_t` and `uint64_t`: glibc defines them as `long`
    /// and `unsigned long` on x86-64, while the Linux kernel's `s64`/`u64`
    /// (and so its `int64_t`/`uint64_t`) are `long long` types. `size_t`
    /// and `ssize_t` are `unsigned long` and `long` on both targets.
    pub const fn int64_t_rank(self) -> LongRank {
        match self {
            Self::X86_64LinuxKernel => LongRank::LongLong,
            Self::X86_64LinuxUserspace => LongRank::Long,
        }
    }

    pub const fn plain_char_is_signed(self) -> bool {
        self.plain_char().is_signed()
    }

    /// Modeled target/build predefines, independent of compiler version.
    /// Compiler-specific feature/version macros are not synthesized.
    pub const fn predefined_macros(self) -> &'static [(&'static str, &'static str)] {
        match self {
            Self::X86_64LinuxKernel => &[
                ("__CHAR_UNSIGNED__", "1"),
                ("__CHAR_BIT__", "8"),
                ("__SIZEOF_POINTER__", "8"),
                ("__SIZEOF_LONG__", "8"),
                ("__SIZEOF_INT__", "4"),
                ("__SIZEOF_SHORT__", "2"),
                ("__SIZEOF_LONG_LONG__", "8"),
                ("__LP64__", "1"),
                ("_LP64", "1"),
                ("__x86_64__", "1"),
                ("__x86_64", "1"),
                ("__amd64__", "1"),
                ("__amd64", "1"),
                ("__linux__", "1"),
                ("__linux", "1"),
                ("linux", "1"),
                ("__unix__", "1"),
                ("__unix", "1"),
                ("unix", "1"),
                ("__KERNEL__", "1"),
                ("__BYTE_ORDER__", "1234"),
                ("__ORDER_LITTLE_ENDIAN__", "1234"),
                ("__ORDER_BIG_ENDIAN__", "4321"),
            ],
            Self::X86_64LinuxUserspace => &[
                ("__CHAR_BIT__", "8"),
                ("__SIZEOF_POINTER__", "8"),
                ("__SIZEOF_LONG__", "8"),
                ("__SIZEOF_INT__", "4"),
                ("__SIZEOF_SHORT__", "2"),
                ("__SIZEOF_LONG_LONG__", "8"),
                ("__LP64__", "1"),
                ("_LP64", "1"),
                ("__x86_64__", "1"),
                ("__x86_64", "1"),
                ("__amd64__", "1"),
                ("__amd64", "1"),
                ("__linux__", "1"),
                ("__linux", "1"),
                ("linux", "1"),
                ("__unix__", "1"),
                ("__unix", "1"),
                ("unix", "1"),
                ("__BYTE_ORDER__", "1234"),
                ("__ORDER_LITTLE_ENDIAN__", "1234"),
                ("__ORDER_BIG_ENDIAN__", "4321"),
            ],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn int64_t_is_long_in_user_space_and_long_long_in_the_kernel() {
        assert_eq!(CTarget::X86_64LinuxUserspace.int64_t_rank(), LongRank::Long);
        assert_eq!(
            CTarget::X86_64LinuxKernel.int64_t_rank(),
            LongRank::LongLong
        );
        assert_eq!(LongRank::Long.max(LongRank::LongLong), LongRank::LongLong);
        assert_eq!(LongRank::Long.max(LongRank::Long), LongRank::Long);
    }

    #[test]
    fn targets_are_a_triple_and_a_mode() {
        let triple = Some(CTarget::TRIPLE);
        assert_eq!(CTarget::from_parts(None, None), Ok(CTarget::SUPPORTED));
        assert_eq!(
            CTarget::from_parts(triple, Some("kernel")),
            Ok(CTarget::X86_64LinuxKernel)
        );
        assert_eq!(
            CTarget::from_parts(triple, Some("userspace")),
            Ok(CTarget::X86_64LinuxUserspace)
        );
        let retired = CTarget::from_parts(Some("x86_64-linux-kernel"), None).unwrap_err();
        assert!(
            retired.contains("retired") && retired.contains("mode `kernel`"),
            "{retired}"
        );
        let unknown = CTarget::from_parts(Some("aarch64-unknown-linux-gnu"), None).unwrap_err();
        assert!(unknown.contains("x86_64-unknown-linux-gnu"), "{unknown}");
        let mode = CTarget::from_parts(triple, Some("bare")).unwrap_err();
        assert!(mode.contains("`kernel`, `userspace`"), "{mode}");
    }

    #[test]
    fn default_target_is_userspace_with_signed_char() {
        let target = CTarget::SUPPORTED;
        assert_eq!(target.mode(), "userspace");
        assert_eq!(target.abi(), CAbi::SUPPORTED);
        assert_eq!(target.char_bits(), 8);
        assert!(target.plain_char_is_signed());
        assert!(!CTarget::X86_64LinuxKernel.plain_char_is_signed());
    }

    #[test]
    fn every_target_predefines_char_unsigned_exactly_when_plain_char_is_unsigned() {
        for target in CTarget::ALL {
            let predefined = target
                .predefined_macros()
                .iter()
                .any(|(name, _)| *name == "__CHAR_UNSIGNED__");
            assert_eq!(
                predefined,
                target.plain_char() == PlainChar::Unsigned,
                "{}",
                target.name()
            );
        }
        assert_eq!(CTarget::X86_64LinuxKernel.plain_char(), PlainChar::Unsigned);
    }

    #[test]
    fn plain_char_ranges_and_character_values_follow_signedness() {
        assert_eq!(PlainChar::Unsigned.range(), (0, 255));
        assert_eq!(PlainChar::Signed.range(), (-128, 127));
        assert_eq!(PlainChar::Unsigned.character_value(0xC8), 200);
        assert_eq!(PlainChar::Signed.character_value(0xC8), -56);
        assert_eq!(PlainChar::Signed.character_value(b'a'), 97);
        assert_eq!(PlainChar::Unsigned.byte_type(), C0Type::UInt8);
        assert_eq!(PlainChar::Signed.byte_type(), C0Type::Int8);
    }

    #[test]
    fn every_target_byte_order_matches_its_byte_order_predefine() {
        for target in CTarget::ALL {
            let predefined = target
                .predefined_macros()
                .iter()
                .find(|(name, _)| *name == "__BYTE_ORDER__")
                .map(|(_, value)| *value);
            let expected = match target.byte_order() {
                ByteOrder::Little => "1234",
                ByteOrder::Big => "4321",
            };
            assert_eq!(predefined, Some(expected), "{}", target.name());
        }
    }

    #[test]
    fn userspace_profile_never_injects_kernel_predefines() {
        let target = CTarget::X86_64LinuxUserspace;
        assert_eq!(target.abi(), CAbi::Lp64);
        assert_eq!(target.char_bits(), 8);
        assert!(target.plain_char_is_signed());
        assert_eq!(target.plain_char(), PlainChar::Signed);
        assert!(
            !target
                .predefined_macros()
                .iter()
                .any(|(name, _)| *name == "__KERNEL__")
        );
    }
}
