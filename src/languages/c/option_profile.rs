//! Named compiler-option profiles for compiler-backed C imports.
//!
//! Without a profile, an import accepts only the preprocessing options
//! `-D`, `-U`, `-I`, `-isystem`, and `-include` beside its target's fixed
//! arguments. A profile names one recorded build's option set: a closed list
//! of exact spellings, each accepted because ignoring it cannot make Click
//! accept a program the compiler treats differently. Each spelling's reason is
//! in the classification table of `docs/reference/cli/import.md`, which a test
//! keeps in step with these lists. There are no prefix or pattern matches: an
//! unknown option, or a known option with another value, is refused.

use super::target::CTarget;

/// A named, closed option set.
#[derive(Debug)]
pub(crate) struct OptionProfile {
    pub(crate) name: &'static str,
    target: CTarget,
    /// Exact spellings accepted under this profile.
    accepted: &'static [&'static str],
    /// Recorded spellings classified as unsound to ignore, with the reason
    /// the refusal reports.
    rejected: &'static [(&'static str, &'static str)],
    /// `(option, required, reason)`: `option` is accepted only in a vector
    /// that also contains `required`.
    requires: &'static [(&'static str, &'static str, &'static str)],
}

/// The option set of the recorded Linux v6.8.12 `x86_64_defconfig` Kbuild
/// compilation of `lib/rbtree.c` with GCC 13.
pub(crate) const LINUX_KBUILD: OptionProfile = OptionProfile {
    name: "linux-6.8-x86_64-kbuild",
    target: CTarget::X86_64LinuxKernel,
    accepted: &[
        // Preprocessing; its effect is in the locked artifact.
        "-fmacro-prefix-map=./=",
        // Diagnostics only.
        "-Wall",
        "-Werror",
        "-Werror=date-time",
        "-Werror=designated-init",
        "-Werror=implicit-function-declaration",
        "-Werror=implicit-int",
        "-Werror=incompatible-pointer-types",
        "-Werror=return-type",
        "-Werror=strict-prototypes",
        "-Wcast-function-type",
        "-Wenum-conversion",
        "-Wframe-larger-than=2048",
        "-Wimplicit-fallthrough=5",
        "-Wmissing-declarations",
        "-Wmissing-prototypes",
        "-Wundef",
        "-Wvla",
        "-Wno-address-of-packed-member",
        "-Wno-alloc-size-larger-than",
        "-Wno-array-bounds",
        "-Wno-dangling-pointer",
        "-Wno-format-overflow",
        "-Wno-format-security",
        "-Wno-format-truncation",
        "-Wno-frame-address",
        "-Wno-main",
        "-Wno-maybe-uninitialized",
        "-Wno-missing-field-initializers",
        "-Wno-override-init",
        "-Wno-packed-not-aligned",
        "-Wno-pointer-sign",
        "-Wno-restrict",
        "-Wno-shift-negative-value",
        "-Wno-sign-compare",
        "-Wno-stringop-overflow",
        "-Wno-stringop-truncation",
        "-Wno-trigraphs",
        "-Wno-type-limits",
        "-Wno-unused-but-set-variable",
        "-Wno-unused-const-variable",
        // Source semantics no weaker than Click's.
        "-fno-common",
        "-fno-delete-null-pointer-checks",
        "-fno-strict-aliasing",
        "-fno-strict-overflow",
        "-fshort-wchar",
        "-fstrict-flex-arrays=3",
        "-ftrivial-auto-var-init=zero",
        "-fno-allow-store-data-races",
        // Code generation only.
        "-falign-functions=16",
        "-falign-jumps=1",
        "-falign-loops=1",
        "-fcf-protection=branch",
        "-fconserve-stack",
        "-fno-PIE",
        "-fno-asynchronous-unwind-tables",
        "-fno-jump-tables",
        "-fno-stack-check",
        "-fno-stack-clash-protection",
        "-fomit-frame-pointer",
        "-fpatchable-function-entry=16,16",
        "-fstack-protector-strong",
        // Target code generation and instruction-set restrictions.
        "-mcmodel=kernel",
        "-mfunction-return=thunk-extern",
        "-mindirect-branch-cs-prefix",
        "-mindirect-branch-register",
        "-mindirect-branch=thunk-extern",
        "-mno-3dnow",
        "-mno-80387",
        "-mno-avx",
        "-mno-fp-ret-in-387",
        "-mno-mmx",
        "-mno-red-zone",
        "-mno-sse",
        "-mno-sse2",
        "-mpreferred-stack-boundary=3",
        "-mskip-rax-setup",
        "-mtune=generic",
    ],
    rejected: &[(
        "-O2",
        "GCC at -O1 and above relies on the `nonnull`, `const`, and `noreturn` function attributes, which Click accepts without modeling: it deletes a `nonnull` parameter's null check even with -fno-delete-null-pointer-checks, merges `const` calls across stores, and drops the code after a `noreturn` call",
    )],
    requires: &[
        (
            "-mno-sse",
            "-mno-80387",
            "without it GCC evaluates floating point on the x87 with excess precision, which Click does not model",
        ),
        (
            "-mno-sse2",
            "-mno-80387",
            "without it GCC evaluates double on the x87 with excess precision, which Click does not model",
        ),
    ],
};

const PROFILES: &[&OptionProfile] = &[&LINUX_KBUILD];

impl OptionProfile {
    /// Resolves a configured profile name for `target`.
    pub(crate) fn named(name: &str, target: CTarget) -> Result<&'static Self, String> {
        let profile = PROFILES
            .iter()
            .copied()
            .find(|profile| profile.name == name)
            .ok_or_else(|| {
                format!(
                    "unknown compiler option profile `{name}`; known profiles: {}",
                    PROFILES
                        .iter()
                        .map(|profile| format!("`{}`", profile.name))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })?;
        if profile.target != target {
            return Err(format!(
                "compiler option profile `{name}` applies only to target `{}`",
                profile.target.name()
            ));
        }
        Ok(profile)
    }

    /// Whether `argument` is one of this profile's exact accepted spellings.
    pub(crate) fn accepts(&self, argument: &str) -> bool {
        self.accepted.contains(&argument)
    }

    /// The reason a recorded spelling stays refused, if it is classified.
    pub(crate) fn rejection(&self, argument: &str) -> Option<&'static str> {
        self.rejected
            .iter()
            .find(|(spelling, _)| *spelling == argument)
            .map(|(_, reason)| *reason)
    }

    /// Checks the requirements between accepted options in one vector.
    pub(crate) fn check_vector(&self, arguments: &[String]) -> Result<(), String> {
        for (option, required, reason) in self.requires {
            let Some(index) = arguments.iter().position(|argument| argument == option) else {
                continue;
            };
            if !arguments.iter().any(|argument| argument == required) {
                return Err(format!(
                    "compiler argument {} `{option}` needs `{required}` in option profile `{}`: {reason}",
                    index + 1,
                    self.name
                ));
            }
        }
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn accepted(&self) -> &'static [&'static str] {
        self.accepted
    }

    #[cfg(test)]
    pub(crate) fn rejected(&self) -> &'static [(&'static str, &'static str)] {
        self.rejected
    }
}
