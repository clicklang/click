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
//! qualifiers, as GCC's pointer alias sets do. A struct is identified by its
//! tag and carries the classes it contains behind one `Arc`, so a class
//! stays small and cloning it never copies a layout.

use std::sync::Arc;

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
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CPointeeBase {
    Void,
    PlainChar,
    SignedChar,
    UnsignedChar,
    Bool,
    Integer { class: CScalarClass, signed: bool },
    Float,
    Double,
    Struct(CStructClass),
}

/// A struct type: its tag, which gives its identity within a translation
/// unit, and what its layout contains when that is known.
#[derive(Clone, Debug)]
pub struct CStructClass(Arc<CStructData>);

#[derive(Debug)]
struct CStructData {
    tag: Arc<str>,
    contents: Option<CStructContents>,
}

/// What a struct contains at any depth, embedded structs and unions
/// included: the class of every scalar and pointer member, and the tag of
/// every embedded struct.
#[derive(Debug)]
struct CStructContents {
    members: Vec<CAccessClass>,
    embedded: Vec<Arc<str>>,
    /// Some pointer member has no class, as a function pointer has; any
    /// pointer access may be reading it.
    unclassed_pointer: bool,
}

/// Collects a struct's contents member by member.
#[derive(Default)]
pub struct CStructContentsBuilder {
    members: Vec<CAccessClass>,
    embedded: Vec<Arc<str>>,
    unclassed_pointer: bool,
}

impl CStructContentsBuilder {
    /// A scalar or pointer member; `None` for a pointer whose class is not
    /// known.
    pub fn member(&mut self, class: Option<CAccessClass>) {
        match class {
            Some(class) => self.members.push(class),
            None => self.unclassed_pointer = true,
        }
    }

    /// An embedded struct, or an array of them, whose contents the struct
    /// absorbs. An embedded struct of unknown layout is only identified.
    pub fn embed(&mut self, inner: CStructClass) {
        if let Some(contents) = &inner.0.contents {
            self.members.extend(contents.members.iter().cloned());
            self.embedded.extend(contents.embedded.iter().cloned());
            self.unclassed_pointer |= contents.unclassed_pointer;
        }
        self.embedded.push(inner.0.tag.clone());
    }

    pub fn build(mut self, tag: impl Into<Arc<str>>) -> CStructClass {
        self.members.sort();
        self.members.dedup();
        self.embedded.sort();
        self.embedded.dedup();
        CStructClass(Arc::new(CStructData {
            tag: tag.into(),
            contents: Some(CStructContents {
                members: self.members,
                embedded: self.embedded,
                unclassed_pointer: self.unclassed_pointer,
            }),
        }))
    }
}

/// The class of a C object or of the lvalue an access uses.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CAccessClass {
    Scalar(CScalarClass),
    /// A pointer to `base` through `depth` levels of indirection: `int *` is
    /// depth 1, `int **` depth 2.
    Pointer {
        base: CPointeeBase,
        depth: u8,
    },
    /// A struct object. No access has this class: a member access names the
    /// struct it goes through as a [`CAccessClass::Member`].
    Struct(CStructClass),
    /// An access through a struct lvalue of type `.0` to a member of class
    /// `.1`, as `p->field` is; the member's class is `None` when it is not
    /// known, as for a function pointer.
    Member(Arc<(CStructClass, Option<CAccessClass>)>),
}

impl std::fmt::Display for CAccessClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Scalar(class) => write!(f, "scalar({class:?})"),
            Self::Struct(class) => write!(f, "struct {}", class.tag()),
            Self::Pointer { base, depth } => {
                write!(f, "pointer(base=")?;
                match base {
                    CPointeeBase::Struct(class) => write!(f, "struct {}", class.tag())?,
                    other => write!(f, "{other:?}")?,
                }
                write!(f, ", depth={depth})")
            }
            Self::Member(member) => {
                write!(f, "member(container=struct {}, class=", member.0.tag())?;
                match &member.1 {
                    Some(class) => write!(f, "{class}")?,
                    None => write!(f, "unknown")?,
                }
                write!(f, ")")
            }
        }
    }
}

impl CStructClass {
    /// A struct whose layout is unknown here, such as the pointee of a
    /// pointer member: its identity is known, its contents are not.
    pub fn opaque(tag: impl Into<Arc<str>>) -> Self {
        Self(Arc::new(CStructData {
            tag: tag.into(),
            contents: None,
        }))
    }

    pub fn tag(&self) -> &str {
        &self.0.tag
    }

    /// Whether a struct of this type embeds one of type `other` at some
    /// depth. An opaque struct may embed anything.
    fn may_embed(&self, other: &Self) -> bool {
        self.0.contents.as_ref().is_none_or(|contents| {
            contents
                .embedded
                .binary_search_by(|tag| tag.as_ref().cmp(other.tag()))
                .is_ok()
        })
    }

    /// Whether some member at some depth may be accessed through `access`.
    /// An opaque struct may contain anything.
    fn may_contain(&self, access: &CAccessClass) -> bool {
        self.0.contents.as_ref().is_none_or(|contents| {
            (contents.unclassed_pointer && matches!(access, CAccessClass::Pointer { .. }))
                || contents
                    .members
                    .iter()
                    .any(|member| access.may_access(member))
        })
    }
}

impl PartialEq for CStructClass {
    fn eq(&self, other: &Self) -> bool {
        self.0.tag == other.0.tag
    }
}

impl Eq for CStructClass {}

impl std::hash::Hash for CStructClass {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.tag.hash(state);
    }
}

impl PartialOrd for CStructClass {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CStructClass {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.tag.cmp(&other.0.tag)
    }
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

    /// A member access through `container` to a member of class `member`.
    pub fn member(container: CStructClass, member: Option<Self>) -> Self {
        Self::Member(Arc::new((container, member)))
    }

    /// The class of the object a pointer of this class points to, when it
    /// is known: `int **` gives `int *`, and `long *` gives `long`. A pointer
    /// to `void` designates an object of unknown class.
    pub fn pointee(&self) -> Option<Self> {
        let (base, depth) = match self {
            Self::Pointer { base, depth } => (base, *depth),
            Self::Member(access) => return access.1.as_ref()?.pointee(),
            Self::Scalar(_) | Self::Struct(_) => return None,
        };
        if depth > 1 {
            return Some(Self::Pointer {
                base: base.clone(),
                depth: depth - 1,
            });
        }
        Some(Self::Scalar(match base {
            CPointeeBase::Struct(class) => return Some(Self::Struct(class.clone())),
            CPointeeBase::Void => return None,
            CPointeeBase::PlainChar | CPointeeBase::SignedChar | CPointeeBase::UnsignedChar => {
                CScalarClass::Char
            }
            CPointeeBase::Bool => CScalarClass::Bool,
            CPointeeBase::Integer { class, .. } => *class,
            CPointeeBase::Float => CScalarClass::Float,
            CPointeeBase::Double => CScalarClass::Double,
        }))
    }

    fn is_character(&self) -> bool {
        match self {
            Self::Scalar(class) => *class == CScalarClass::Char,
            Self::Member(access) => access.1.as_ref().is_some_and(Self::is_character),
            Self::Pointer { .. } | Self::Struct(_) => false,
        }
    }

    /// Whether an access of class `self` may read or write an object of
    /// class `object` (C11 6.5p7). A character access may touch any object;
    /// otherwise the classes must agree, except that `void *` agrees with
    /// every pointer class. A struct object admits an access of a class one
    /// of its members has. A member access through struct `S` requires the
    /// object to be an `S`, a struct embedding `S`, or a struct `S` embeds,
    /// the last because a pointer may know only part of the object, as a
    /// `container_of` from a member's pointer does; through `S` a scalar
    /// object admits the access its member class would make.
    pub fn may_access(&self, object: &Self) -> bool {
        if self.is_character() || self == object {
            return true;
        }
        match (self, object) {
            (Self::Member(access), Self::Struct(object)) => {
                let container = &access.0;
                container == object || object.may_embed(container) || container.may_embed(object)
            }
            (Self::Member(access), _) => access
                .1
                .as_ref()
                .is_none_or(|member| member.may_access(object)),
            (_, Self::Struct(object)) => object.may_contain(self),
            (Self::Pointer { .. }, Self::Pointer { .. }) => {
                *self == Self::VOID_POINTER || *object == Self::VOID_POINTER
            }
            // No access has a struct class, and no object a member class.
            (Self::Struct(_), _) | (_, Self::Member(_)) => true,
            _ => false,
        }
    }

    /// Whether a pointer whose pointee has class `self`, as a parameter
    /// declares, may designate an object of class `object`: whether the
    /// accesses that pointer's type makes are allowed on it. A struct pointee
    /// is consistent with what a member access through that struct may
    /// touch, so a pointer to a member of an enclosing struct is accepted.
    pub fn may_designate(&self, object: &Self) -> bool {
        match self {
            Self::Struct(container) => Self::member(container.clone(), None).may_access(object),
            _ => self.may_access(object),
        }
    }

    /// The C spelling of the class, for diagnostics. A member access is
    /// spelled as the struct it goes through.
    pub fn spelling(&self) -> String {
        match self {
            Self::Scalar(class) => class.spelling().to_string(),
            Self::Pointer { base, depth } => {
                format!("{} {}", base.spelling(), "*".repeat(usize::from(*depth)))
            }
            Self::Struct(class) => class.spelling(),
            Self::Member(access) => access.0.spelling(),
        }
    }
}

impl CStructClass {
    fn spelling(&self) -> String {
        format!("struct {}", self.0.tag)
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
    fn spelling(&self) -> String {
        match self {
            Self::Void => "void".to_string(),
            Self::PlainChar => "char".to_string(),
            Self::SignedChar => "signed char".to_string(),
            Self::UnsignedChar => "unsigned char".to_string(),
            Self::Bool => "_Bool".to_string(),
            Self::Integer { class, signed } => {
                let name = class.spelling();
                if *signed {
                    name.to_string()
                } else {
                    format!("unsigned {name}")
                }
            }
            Self::Float => "float".to_string(),
            Self::Double => "double".to_string(),
            Self::Struct(class) => class.spelling(),
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
        assert!(LONG.may_access(&LONG));
        assert!(!LONG_LONG.may_access(&LONG));
        assert!(!LONG.may_access(&LONG_LONG));
        // A character access may touch anything; nothing else may touch a
        // character object.
        assert!(CHAR.may_access(&LONG));
        assert!(!CAccessClass::Scalar(CScalarClass::Int).may_access(&CHAR));
    }

    #[test]
    fn pointer_classes_follow_gcc_alias_sets() {
        let int_pointer = pointer(CScalarClass::Int, true, 1);
        assert!(int_pointer.may_access(&int_pointer));
        assert!(!int_pointer.may_access(&pointer(CScalarClass::Int, false, 1)));
        assert!(!int_pointer.may_access(&pointer(CScalarClass::Long, true, 1)));
        assert!(!int_pointer.may_access(&pointer(CScalarClass::Int, true, 2)));
        assert!(CAccessClass::VOID_POINTER.may_access(&int_pointer));
        assert!(int_pointer.may_access(&CAccessClass::VOID_POINTER));
        assert_eq!(
            pointer(CScalarClass::Int, false, 2).spelling(),
            "unsigned int **"
        );
    }

    fn int_struct(tag: &str) -> CStructClass {
        let mut contents = CStructContentsBuilder::default();
        contents.member(Some(CAccessClass::Scalar(CScalarClass::Int)));
        contents.build(tag)
    }

    #[test]
    fn member_accesses_follow_their_struct() {
        const INT: CAccessClass = CAccessClass::Scalar(CScalarClass::Int);
        let a = int_struct("a");
        let b = int_struct("b");
        let mut outer = CStructContentsBuilder::default();
        outer.embed(a.clone());
        outer.member(Some(LONG));
        let outer = outer.build("outer");
        let through = |container: &CStructClass| CAccessClass::member(container.clone(), Some(INT));
        // Same layout, distinct types.
        assert!(!through(&b).may_access(&CAccessClass::Struct(a.clone())));
        assert!(through(&a).may_access(&CAccessClass::Struct(a.clone())));
        // A struct embedding the container, and a container embedding the
        // object, as `container_of` makes.
        assert!(through(&a).may_access(&CAccessClass::Struct(outer.clone())));
        assert!(through(&outer).may_access(&CAccessClass::Struct(a.clone())));
        // A scalar object admits the member's own class.
        assert!(through(&a).may_access(&INT));
        assert!(!through(&a).may_access(&LONG));
        // A struct object admits the classes of its members at any depth.
        assert!(INT.may_access(&CAccessClass::Struct(outer.clone())));
        assert!(LONG.may_access(&CAccessClass::Struct(outer.clone())));
        assert!(!LONG_LONG.may_access(&CAccessClass::Struct(outer)));
        assert!(CHAR.may_access(&CAccessClass::Struct(b)));
        // An opaque struct is only identified.
        assert!(LONG_LONG.may_access(&CAccessClass::Struct(CStructClass::opaque("a"))));
    }

    #[test]
    fn unclassed_pointer_members_admit_any_pointer_access() {
        let mut contents = CStructContentsBuilder::default();
        contents.member(None);
        let callbacks = CAccessClass::Struct(contents.build("ops"));
        assert!(pointer(CScalarClass::Int, true, 1).may_access(&callbacks));
        assert!(!LONG.may_access(&callbacks));
    }
}
