//! Access classes for the strict-aliasing check (`design/effective-types.md`).
//!
//! C11 6.5p7 lets an object be accessed only through a type compatible with
//! its own, up to signedness and qualifiers, or through a character type.
//! GCC relies on that rule at `-O2`. The kernel's memory model checks widths
//! and layouts, under which `long` and `long long`, or two pointer types, are
//! interchangeable; an access class carries the distinctions the rule makes.
//!
//! A scalar class erases signedness and qualifiers. A pointer class keeps its
//! pointee type, signedness included, and erases only the pointee's
//! qualifiers, as GCC's pointer alias sets do. Every class is small and
//! `Copy`, so carrying one costs no allocation.

/// The integer and floating classes of a scalar object or access.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CScalarClass {
    /// Plain `char`, `signed char` or `unsigned char`, which alias every
    /// object.
    Char,
    Bool,
    Short,
    Int,
    Long,
    LongLong,
    Int128,
    Float,
    Double,
}

/// The non-pointer type a pointer class points to, with signedness kept.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CPointeeBase {
    Void,
    PlainChar,
    SignedChar,
    UnsignedChar,
    Bool,
    Integer { class: CScalarClass, signed: bool },
    Float,
    Double,
}

/// The class of a C object or of the lvalue an access uses.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CAccessClass {
    Scalar(CScalarClass),
    /// A pointer to `base` through `depth` levels of indirection: `int *` is
    /// depth 1, `int **` depth 2.
    Pointer {
        base: CPointeeBase,
        depth: u8,
    },
}

impl CAccessClass {
    /// The class of `void *`, which is compatible with every pointer class.
    pub const VOID_POINTER: Self = Self::Pointer {
        base: CPointeeBase::Void,
        depth: 1,
    };

    /// The class a kernel type determines on its own, when it determines
    /// one. The kernel type erases `long` versus `long long`, the pointee of
    /// a struct pointer, which it spells as an `int32` pointer, and plain
    /// versus explicitly signed `char` pointees, so those give `None`: an
    /// access whose class is unknown is not checked.
    pub fn of_kernel_type(c_type: crate::kernel::CType) -> Option<Self> {
        use crate::kernel::CType;
        Some(match c_type {
            CType::Bool => Self::Scalar(CScalarClass::Bool),
            CType::Int8 | CType::UInt8 => Self::Scalar(CScalarClass::Char),
            CType::Int16 | CType::UInt16 => Self::Scalar(CScalarClass::Short),
            CType::Int32 | CType::UInt32 => Self::Scalar(CScalarClass::Int),
            CType::Int128 | CType::UInt128 => Self::Scalar(CScalarClass::Int128),
            CType::Float32 => Self::Scalar(CScalarClass::Float),
            CType::Float64 => Self::Scalar(CScalarClass::Double),
            CType::VoidPointer => Self::VOID_POINTER,
            _ => return None,
        })
    }

    /// The class of the object a pointer of this class points to, when it
    /// is known: `int **` gives `int *`, and `long *` gives `long`. A pointer
    /// to `void` designates an object of unknown class.
    pub fn pointee(self) -> Option<Self> {
        let Self::Pointer { base, depth } = self else {
            return None;
        };
        if depth > 1 {
            return Some(Self::Pointer {
                base,
                depth: depth - 1,
            });
        }
        Some(Self::Scalar(match base {
            CPointeeBase::Void => return None,
            CPointeeBase::PlainChar | CPointeeBase::SignedChar | CPointeeBase::UnsignedChar => {
                CScalarClass::Char
            }
            CPointeeBase::Bool => CScalarClass::Bool,
            CPointeeBase::Integer { class, .. } => class,
            CPointeeBase::Float => CScalarClass::Float,
            CPointeeBase::Double => CScalarClass::Double,
        }))
    }

    fn is_character(self) -> bool {
        matches!(self, Self::Scalar(CScalarClass::Char))
    }

    /// Whether an access of class `self` may read or write an object of
    /// class `object` (C11 6.5p7). A character access may touch any object;
    /// otherwise the classes must agree, except that `void *` agrees with
    /// every pointer class.
    pub fn may_access(self, object: Self) -> bool {
        if self.is_character() || self == object {
            return true;
        }
        matches!(
            (self, object),
            (Self::Pointer { .. }, Self::Pointer { .. })
                if self == Self::VOID_POINTER || object == Self::VOID_POINTER
        )
    }

    /// The C spelling of the class, for diagnostics.
    pub fn spelling(self) -> String {
        match self {
            Self::Scalar(class) => class.spelling().to_string(),
            Self::Pointer { base, depth } => {
                format!("{} {}", base.spelling(), "*".repeat(usize::from(depth)))
            }
        }
    }
}

impl CScalarClass {
    fn spelling(self) -> &'static str {
        match self {
            Self::Char => "char",
            Self::Bool => "_Bool",
            Self::Short => "short",
            Self::Int => "int",
            Self::Long => "long",
            Self::LongLong => "long long",
            Self::Int128 => "__int128",
            Self::Float => "float",
            Self::Double => "double",
        }
    }
}

impl CPointeeBase {
    fn spelling(self) -> String {
        match self {
            Self::Void => "void".to_string(),
            Self::PlainChar => "char".to_string(),
            Self::SignedChar => "signed char".to_string(),
            Self::UnsignedChar => "unsigned char".to_string(),
            Self::Bool => "_Bool".to_string(),
            Self::Integer { class, signed } => {
                let name = class.spelling();
                if signed {
                    name.to_string()
                } else {
                    format!("unsigned {name}")
                }
            }
            Self::Float => "float".to_string(),
            Self::Double => "double".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const LONG: CAccessClass = CAccessClass::Scalar(CScalarClass::Long);
    const LONG_LONG: CAccessClass = CAccessClass::Scalar(CScalarClass::LongLong);
    const CHAR: CAccessClass = CAccessClass::Scalar(CScalarClass::Char);

    fn pointer(class: CScalarClass, signed: bool, depth: u8) -> CAccessClass {
        CAccessClass::Pointer {
            base: CPointeeBase::Integer { class, signed },
            depth,
        }
    }

    #[test]
    fn scalars_follow_c11_6_5p7() {
        assert!(LONG.may_access(LONG));
        assert!(!LONG_LONG.may_access(LONG));
        assert!(!LONG.may_access(LONG_LONG));
        // A character access may touch anything; nothing else may touch a
        // character object.
        assert!(CHAR.may_access(LONG));
        assert!(!CAccessClass::Scalar(CScalarClass::Int).may_access(CHAR));
    }

    #[test]
    fn pointer_classes_follow_gcc_alias_sets() {
        let int_pointer = pointer(CScalarClass::Int, true, 1);
        assert!(int_pointer.may_access(int_pointer));
        assert!(!int_pointer.may_access(pointer(CScalarClass::Int, false, 1)));
        assert!(!int_pointer.may_access(pointer(CScalarClass::Long, true, 1)));
        assert!(!int_pointer.may_access(pointer(CScalarClass::Int, true, 2)));
        assert!(CAccessClass::VOID_POINTER.may_access(int_pointer));
        assert!(int_pointer.may_access(CAccessClass::VOID_POINTER));
        assert_eq!(
            pointer(CScalarClass::Int, false, 2).spelling(),
            "unsigned int **"
        );
    }
}
