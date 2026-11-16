use super::*;

/// Prepared source ownership shared by every declaration of a function.
#[derive(Clone, Debug)]
pub struct LocalFunctionId(Arc<LocalFunctionIdentity>);
#[derive(Debug)]
struct LocalFunctionIdentity {
    source: Option<String>,
    function: String,
    fingerprint: u64,
}
impl LocalFunctionId {
    pub fn new(source: Option<String>, function: String) -> Self {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        (&source, &function).hash(&mut hasher);
        Self(Arc::new(LocalFunctionIdentity {
            source,
            function,
            fingerprint: hasher.finish(),
        }))
    }
    fn identity(&self) -> (&Option<String>, &str) {
        (&self.0.source, &self.0.function)
    }
}
impl PartialEq for LocalFunctionId {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.identity() == other.identity()
    }
}
impl Eq for LocalFunctionId {}
impl PartialOrd for LocalFunctionId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for LocalFunctionId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            std::cmp::Ordering::Equal
        } else {
            self.identity().cmp(&other.identity())
        }
    }
}
impl Hash for LocalFunctionId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.fingerprint.hash(state);
    }
}

/// A declaration's identity within a prepared C function. Its source spelling
/// is metadata, never part of the identity used for storage or execution.
#[derive(Clone, Debug)]
pub struct LocalBindingId(Arc<LocalDeclaration>);
#[derive(Debug)]
struct LocalDeclaration {
    owner: LocalFunctionId,
    parameter: bool,
    temporary: bool,
    ordinal: u32,
    scope_depth: u32,
    spelling: Option<String>,
    program_type: OnceLock<ProgramType>,
    array_shape: OnceLock<Arc<[u32]>>,
    struct_name: OnceLock<Arc<str>>,
}
impl LocalBindingId {
    pub fn new(
        owner: LocalFunctionId,
        parameter: bool,
        ordinal: u32,
        spelling: Option<String>,
    ) -> Self {
        Self(Arc::new(LocalDeclaration {
            owner,
            parameter,
            temporary: false,
            ordinal,
            scope_depth: 0,
            spelling,
            program_type: OnceLock::new(),
            array_shape: OnceLock::new(),
            struct_name: OnceLock::new(),
        }))
    }
    /// A frontend temporary is distinct from all source declaration ordinals.
    pub(crate) fn temporary(owner: LocalFunctionId, ordinal: u32) -> Self {
        Self(Arc::new(LocalDeclaration {
            owner,
            parameter: false,
            temporary: true,
            ordinal,
            scope_depth: 0,
            spelling: None,
            program_type: OnceLock::new(),
            array_shape: OnceLock::new(),
            struct_name: OnceLock::new(),
        }))
    }
    pub fn is_temporary(&self) -> bool {
        self.0.temporary
    }
    pub(crate) fn with_scope_depth(self, scope_depth: u32) -> Self {
        Self(Arc::new(LocalDeclaration {
            owner: self.0.owner.clone(),
            parameter: self.0.parameter,
            temporary: self.0.temporary,
            ordinal: self.0.ordinal,
            scope_depth,
            spelling: self.0.spelling.clone(),
            program_type: OnceLock::new(),
            array_shape: OnceLock::new(),
            struct_name: OnceLock::new(),
        }))
    }
    pub fn owner(&self) -> &LocalFunctionId {
        &self.0.owner
    }
    pub fn scope_depth(&self) -> u32 {
        self.0.scope_depth
    }
    pub fn source(&self) -> Option<&str> {
        self.0.owner.0.source.as_deref()
    }
    pub fn function(&self) -> &str {
        &self.0.owner.0.function
    }
    pub fn ordinal(&self) -> u32 {
        self.0.ordinal
    }
    pub fn is_parameter(&self) -> bool {
        self.0.parameter
    }
    pub fn spelling(&self) -> Option<&str> {
        self.0.spelling.as_deref()
    }
    /// Source type metadata is filled by the C declaration builder before lowering.
    pub(crate) fn initialize_program_type(&self, ty: ProgramType) {
        let _ = self.0.program_type.set(ty);
    }
    pub(crate) fn initialize_array_shape(&self, shape: &[u32]) {
        let _ = self.0.array_shape.set(Arc::from(shape));
    }
    pub(crate) fn initialize_struct_name(&self, name: &str) {
        let _ = self.0.struct_name.set(Arc::from(name));
    }
    pub fn array_shape(&self) -> Option<&[u32]> {
        self.0.array_shape.get().map(|shape| shape.as_ref())
    }
    pub fn struct_name(&self) -> Option<&str> {
        self.0.struct_name.get().map(|name| name.as_ref())
    }
    pub fn program_type(&self) -> Option<ProgramType> {
        self.0.program_type.get().copied()
    }
    fn identity(&self) -> (&LocalFunctionId, bool, bool, u32) {
        (
            &self.0.owner,
            self.0.temporary,
            self.0.parameter,
            self.0.ordinal,
        )
    }
}

impl PartialEq for LocalBindingId {
    fn eq(&self, other: &Self) -> bool {
        self.identity() == other.identity()
    }
}
impl Eq for LocalBindingId {}
impl PartialOrd for LocalBindingId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for LocalBindingId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.identity().cmp(&other.identity())
    }
}
impl Hash for LocalBindingId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if self.is_temporary() {
            (&self.0.owner, 2u8, self.0.ordinal).hash(state);
        } else {
            // Preserve the hash domain of existing C declaration identities.
            (&self.0.owner, self.0.parameter, self.0.ordinal).hash(state);
        }
    }
}
impl std::fmt::Display for LocalBindingId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(source) = self.source() {
            write!(f, "{source:?}::")?;
        }
        write!(
            f,
            "{}.{}({})",
            self.function(),
            if self.is_temporary() {
                "temporary"
            } else if self.is_parameter() {
                "parameter"
            } else {
                "local"
            },
            self.ordinal()
        )
    }
}

/// A specification binder identity occupies a separate namespace from source
/// names and C declarations. Cloning a term retains its lexical identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct GeneratedBinderId(u64);
// Explicit numeric spellings and internally allocated names share a typed namespace.
// Reserve intervals so sparse user spellings do not exhaust or linearly probe it.
#[derive(Default)]
struct BinderIds {
    next: u64,
    reserved: std::collections::BTreeMap<u64, u64>,
}
impl BinderIds {
    fn reserve(&mut self, number: u64) {
        let mut start = number;
        let mut end = number;
        if let Some((&left, &right)) = self.reserved.range(..=number).next_back() {
            if right >= number {
                return;
            }
            if right.checked_add(1) == Some(number) {
                start = left;
                self.reserved.remove(&left);
            }
        }
        if let Some((&left, &right)) = self.reserved.range(number..).next() {
            if number.checked_add(1) == Some(left) {
                end = right;
                self.reserved.remove(&left);
            }
        }
        self.reserved.insert(start, end);
    }
    fn fresh(&mut self) -> u64 {
        if let Some((_, &end)) = self.reserved.range(..=self.next).next_back() {
            if end >= self.next {
                self.next = end
                    .checked_add(1)
                    .expect("specification binder identity space exhausted");
            }
        }
        let number = self.next;
        self.reserve(number);
        self.next = number
            .checked_add(1)
            .expect("specification binder identity space exhausted");
        number
    }
}
fn binder_ids() -> &'static std::sync::Mutex<BinderIds> {
    static IDS: std::sync::OnceLock<std::sync::Mutex<BinderIds>> = std::sync::OnceLock::new();
    IDS.get_or_init(|| {
        std::sync::Mutex::new(BinderIds {
            next: 1,
            ..Default::default()
        })
    })
}
impl GeneratedBinderId {
    pub(crate) fn fresh() -> Self {
        crate::instrumentation::record_deterministic_work(1);
        Self(binder_ids().lock().unwrap().fresh())
    }
    pub(crate) fn from_spelling(number: u64) -> Self {
        binder_ids().lock().unwrap().reserve(number);
        Self(number)
    }
    pub fn number(self) -> u64 {
        self.0
    }
    pub fn binding_name(self) -> BindingName {
        BindingName::Generated(self)
    }
}
impl std::fmt::Display for GeneratedBinderId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "binder({})", self.0)
    }
}

/// The C declaration owning static storage. File ownership uses the root
/// translation unit, including for declarations brought in through a header.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum StaticBindingOwner {
    File(Option<String>),
    Function(LocalFunctionId),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct StaticBindingMetadata {
    pub program_type: ProgramType,
    pub array_shape: Option<Arc<[u32]>>,
    pub struct_name: Option<Arc<str>>,
    pub aggregate: bool,
    pub volatile: bool,
    pub pointee_volatile: bool,
    pub constant: bool,
    pub pointee_constant: bool,
}

/// Stable identity of one static object; metadata is prepared from the final
/// compatible declaration and is excluded from storage identity.
#[derive(Clone, Debug)]
pub struct StaticBindingId(Arc<StaticDeclaration>);
#[derive(Debug)]
struct StaticDeclaration {
    owner: StaticBindingOwner,
    ordinal: u32,
    spelling: String,
    fingerprint: u64,
    metadata: OnceLock<StaticBindingMetadata>,
    struct_name: OnceLock<Arc<str>>,
}
impl StaticBindingId {
    pub fn new(owner: StaticBindingOwner, ordinal: u32, spelling: String) -> Self {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        (&owner, ordinal).hash(&mut hasher);
        Self(Arc::new(StaticDeclaration {
            owner,
            ordinal,
            spelling,
            fingerprint: hasher.finish(),
            metadata: OnceLock::new(),
            struct_name: OnceLock::new(),
        }))
    }
    pub fn owner(&self) -> &StaticBindingOwner {
        &self.0.owner
    }
    pub fn ordinal(&self) -> u32 {
        self.0.ordinal
    }
    pub fn spelling(&self) -> &str {
        &self.0.spelling
    }
    pub fn source(&self) -> Option<&str> {
        match &self.0.owner {
            StaticBindingOwner::File(source) => source.as_deref(),
            StaticBindingOwner::Function(owner) => owner.0.source.as_deref(),
        }
    }
    pub fn function(&self) -> Option<&str> {
        match &self.0.owner {
            StaticBindingOwner::File(_) => None,
            StaticBindingOwner::Function(owner) => Some(&owner.0.function),
        }
    }
    pub(crate) fn initialize_metadata(&self, metadata: StaticBindingMetadata) {
        let _ = self.0.metadata.set(metadata);
    }
    pub fn metadata(&self) -> Option<&StaticBindingMetadata> {
        self.0.metadata.get()
    }
    pub fn program_type(&self) -> Option<ProgramType> {
        self.metadata().map(|m| m.program_type)
    }
    pub fn array_shape(&self) -> Option<&[u32]> {
        self.metadata()?.array_shape.as_deref()
    }
    pub(crate) fn initialize_struct_name(&self, name: &str) {
        let _ = self.0.struct_name.set(Arc::from(name));
    }
    pub fn struct_name(&self) -> Option<&str> {
        self.0
            .struct_name
            .get()
            .map(AsRef::as_ref)
            .or_else(|| self.metadata()?.struct_name.as_deref())
    }
    fn identity(&self) -> (&StaticBindingOwner, u32) {
        (&self.0.owner, self.0.ordinal)
    }
}
impl PartialEq for StaticBindingId {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.identity() == other.identity()
    }
}
impl Eq for StaticBindingId {}
impl PartialOrd for StaticBindingId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for StaticBindingId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.identity().cmp(&other.identity())
    }
}
impl Hash for StaticBindingId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.fingerprint.hash(state);
    }
}
impl std::fmt::Display for StaticBindingId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(source) = self.source() {
            write!(f, "{source:?}::")?;
        }
        if let Some(function) = self.function() {
            write!(f, "{function}.")?;
        }
        write!(f, "static({})", self.ordinal())
    }
}

/// Named bindings remain available to the other frontends and proof/model
/// binders. C automatic objects always use the declaration alternative.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum BindingName {
    Named(String),
    Local(LocalBindingId),
    Static(StaticBindingId),
    /// The current contract's return value; never a source declaration.
    ContractResult,
    /// The current exceptional postcondition's payload; never a declaration.
    ContractException,
    /// A lexical proof binder, never a program object.
    Generated(GeneratedBinderId),
}

impl BindingName {
    /// A lexical source spelling, absent for frontend temporaries and outcomes.
    pub fn source_spelling(&self) -> Option<&str> {
        match self {
            Self::Named(name) => Some(name),
            Self::Local(id) => id.spelling(),
            Self::Static(id) => Some(id.spelling()),
            Self::ContractResult | Self::ContractException | Self::Generated(_) => None,
        }
    }
    pub fn source_name(&self) -> &str {
        match self {
            Self::Named(name) => name,
            Self::Local(id) => id.spelling().unwrap_or(""),
            Self::Static(id) => id.spelling(),
            Self::ContractResult => "result",
            Self::ContractException => "exception",
            Self::Generated(_) => "",
        }
    }
    pub fn static_id(&self) -> Option<&StaticBindingId> {
        match self {
            Self::Static(id) => Some(id),
            _ => None,
        }
    }
    pub fn program_type(&self) -> Option<ProgramType> {
        match self {
            Self::ContractException => Some(ProgramType::Int32),
            Self::Local(id) => id.program_type(),
            Self::Static(id) => id.program_type(),
            _ => None,
        }
    }
    pub fn array_shape(&self) -> Option<&[u32]> {
        match self {
            Self::Local(id) => id.array_shape(),
            Self::Static(id) => id.array_shape(),
            _ => None,
        }
    }
    pub fn struct_name(&self) -> Option<&str> {
        match self {
            Self::Local(id) => id.struct_name(),
            Self::Static(id) => id.struct_name(),
            _ => None,
        }
    }
    pub fn local_id(&self) -> Option<&LocalBindingId> {
        match self {
            Self::Local(id) => Some(id),
            _ => None,
        }
    }
    pub fn named(&self) -> Option<&str> {
        match self {
            Self::Named(name) => Some(name),
            _ => None,
        }
    }
}

/// Declaration metadata participates in program identity (including source
/// spelling changes), while storage and references use only `reference`.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct BindingDeclaration {
    reference: BindingName,
    spelling: Option<Arc<str>>,
    array_shape: Option<Arc<[u32]>>,
    struct_name: Option<Arc<str>>,
    scope_depth: u32,
    static_metadata: Option<Arc<StaticBindingMetadata>>,
}
impl BindingDeclaration {
    pub fn binding(&self) -> &BindingName {
        &self.reference
    }
    pub fn spelling(&self) -> Option<&str> {
        self.spelling.as_deref()
    }
    pub fn source_name(&self) -> &str {
        self.spelling().unwrap_or("")
    }
}
impl From<BindingName> for BindingDeclaration {
    fn from(reference: BindingName) -> Self {
        let spelling = match &reference {
            BindingName::Named(name) => Some(Arc::from(name.as_str())),
            BindingName::Local(id) => id.spelling().map(Arc::from),
            BindingName::Static(id) => Some(Arc::from(id.spelling())),
            BindingName::ContractResult => Some(Arc::from("result")),
            BindingName::ContractException => Some(Arc::from("exception")),
            BindingName::Generated(_) => None,
        };
        let scope_depth = reference.local_id().map_or(0, LocalBindingId::scope_depth);
        let array_shape = reference.array_shape().map(Arc::from);
        let struct_name = reference.struct_name().map(Arc::from);
        let static_metadata = reference
            .static_id()
            .and_then(StaticBindingId::metadata)
            .map(|metadata| Arc::new(metadata.clone()));
        Self {
            static_metadata,
            reference,
            spelling,
            array_shape,
            struct_name,
            scope_depth,
        }
    }
}
impl From<&BindingDeclaration> for BindingName {
    fn from(declaration: &BindingDeclaration) -> Self {
        declaration.reference.clone()
    }
}
impl From<BindingDeclaration> for BindingName {
    fn from(declaration: BindingDeclaration) -> Self {
        declaration.reference
    }
}
impl std::ops::Deref for BindingDeclaration {
    type Target = BindingName;
    fn deref(&self) -> &BindingName {
        &self.reference
    }
}
impl std::fmt::Display for BindingDeclaration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.reference.fmt(f)
    }
}
impl From<String> for BindingName {
    fn from(name: String) -> Self {
        Self::Named(name)
    }
}
impl From<&str> for BindingName {
    fn from(name: &str) -> Self {
        Self::Named(name.to_owned())
    }
}
impl From<&String> for BindingName {
    fn from(name: &String) -> Self {
        Self::Named(name.clone())
    }
}
impl From<&BindingName> for BindingName {
    fn from(name: &BindingName) -> Self {
        name.clone()
    }
}
impl From<LocalBindingId> for BindingName {
    fn from(id: LocalBindingId) -> Self {
        Self::Local(id)
    }
}
impl std::fmt::Display for BindingName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Named(name) => f.write_str(name),
            Self::Local(id) => id.fmt(f),
            Self::Static(id) => id.fmt(f),
            Self::ContractResult => f.write_str("result"),
            Self::ContractException => f.write_str("exception"),
            Self::Generated(id) => id.fmt(f),
        }
    }
}

/// Per-execution storage identity, independent of the declaration and spelling.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum LocalStorageInstance {
    Implicit,
    ValueParameter,
    Lifetime(u64),
    Frame(u64),
}

impl From<std::sync::Arc<str>> for BindingName {
    fn from(name: std::sync::Arc<str>) -> Self {
        Self::Named(name.to_string())
    }
}
impl From<&std::sync::Arc<str>> for BindingName {
    fn from(name: &std::sync::Arc<str>) -> Self {
        Self::Named(name.to_string())
    }
}
impl BindingName {
    pub fn is_named(&self, name: &str) -> bool {
        self.named() == Some(name)
    }
    pub(crate) fn named_in<'a, T>(&self, map: &'a impl NamedBindingMap<T>) -> Option<&'a T> {
        map.get_binding(self)
    }
}

pub(crate) trait NamedBindingMap<T> {
    fn get_named(&self, name: &str) -> Option<&T>;
    fn get_binding(&self, name: &BindingName) -> Option<&T> {
        name.named().and_then(|name| self.get_named(name))
    }
}
impl<T> NamedBindingMap<T> for BTreeMap<String, T> {
    fn get_named(&self, name: &str) -> Option<&T> {
        self.get(name)
    }
}
impl<T> NamedBindingMap<T> for crate::persistent::PersistentMap<String, T> {
    fn get_named(&self, name: &str) -> Option<&T> {
        self.get(name)
    }
}

impl From<&&BindingName> for BindingName {
    fn from(name: &&BindingName) -> Self {
        (*name).clone()
    }
}

impl std::fmt::Display for LocalStorageInstance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Implicit => f.write_str("implicit"),
            Self::ValueParameter => f.write_str("parameter"),
            Self::Lifetime(id) => write!(f, "lifetime, {id}"),
            Self::Frame(id) => write!(f, "frame, {id}"),
        }
    }
}

impl From<String> for BindingDeclaration {
    fn from(name: String) -> Self {
        BindingName::from(name).into()
    }
}
impl From<&str> for BindingDeclaration {
    fn from(name: &str) -> Self {
        BindingName::from(name).into()
    }
}

impl From<StaticBindingId> for BindingName {
    fn from(id: StaticBindingId) -> Self {
        Self::Static(id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn local(owner: &LocalFunctionId, ordinal: u32, name: &str, depth: u32) -> BindingName {
        LocalBindingId::new(owner.clone(), false, ordinal, Some(name.into()))
            .with_scope_depth(depth)
            .into()
    }

    #[test]
    fn temporary_ids_are_distinct_from_declarations_and_legacy_spellings() {
        let owner = LocalFunctionId::new(Some("unit.cpp".into()), "f".into());
        let temporary: BindingName = LocalBindingId::temporary(owner.clone(), 0).into();
        let source = local(&owner, 0, "__click_cpp_return_value", 0);
        let parameter: BindingName =
            LocalBindingId::new(owner.clone(), true, 0, Some("p".into())).into();
        let mut locals = LocalEnvironment::new();
        locals.set(&temporary, int32(7));
        for (index, binding) in [
            source.clone(),
            parameter,
            "__click_cpp_return_value".into(),
            "__click_cpp_unwind_exception".into(),
            "__click_cpp_nested_value_0".into(),
        ]
        .into_iter()
        .enumerate()
        {
            assert_ne!(temporary, binding);
            locals.set(&binding, int32(index as u32));
            assert_eq!(locals.get(&temporary).unwrap().native().as_ref(), &int32(7));
            assert!(
                Memory::local_pointer(&temporary)
                    .block
                    .proven_distinct(&Memory::local_pointer(binding).block)
            );
        }
        assert_eq!(temporary.source_spelling(), None);
        assert_eq!(locals.active_source_name(&temporary), None);
        assert_eq!(locals.resolve_binding(&temporary), temporary);
        assert_eq!(temporary.to_string(), "\"unit.cpp\"::f.temporary(0)");
        assert_ne!(temporary, BindingName::from(temporary.to_string()));
        assert_ne!(temporary, LocalBindingId::temporary(owner, 1).into());
        assert_ne!(
            temporary,
            LocalBindingId::temporary(
                LocalFunctionId::new(Some("other.cpp".into()), "f".into()),
                0
            )
            .into()
        );
    }

    #[test]
    fn contract_result_is_neither_a_source_name_nor_a_string_alias() {
        let owner = LocalFunctionId::new(None, "f".into());
        let source = local(&owner, 0, "result", 1);
        let mut locals = LocalEnvironment::new();
        locals.set(&source, int32(3));
        locals.bind_logical_typed("result", int32(7), ProgramType::Int32);
        locals.set(CONTRACT_RESULT, int32(11));
        locals.set("@click:result", int32(13));
        for (name, expected) in [
            (source.clone(), 3),
            (BindingName::from("result"), 7),
            (CONTRACT_RESULT, 11),
            (BindingName::from("@click:result"), 13),
        ] {
            assert_eq!(
                locals.get(&name).unwrap().native().as_ref(),
                &int32(expected)
            );
            assert_eq!(locals.resolve_binding(&name), name);
        }
        assert_eq!(locals.active_source_name(&CONTRACT_RESULT), None);
        assert_eq!(CONTRACT_RESULT.named(), None);
        assert_eq!(CONTRACT_RESULT.to_string(), "result");
        let result_slot = Memory::local_pointer(CONTRACT_RESULT);
        assert_eq!(result_slot.block, PointerBlock::ContractResult);
        for binding in [
            source,
            BindingName::from("result"),
            BindingName::from("@click:result"),
        ] {
            assert!(
                result_slot
                    .block
                    .proven_distinct(&Memory::local_pointer(binding).block)
            );
        }
    }

    #[test]
    fn contract_exception_is_neither_a_source_name_nor_a_string_alias() {
        let owner = LocalFunctionId::new(None, "f".into());
        let source = local(&owner, 0, "exception", 1);
        let mut locals = LocalEnvironment::new();
        locals.set(&source, int32(3));
        locals.bind_logical_typed("exception", int32(7), ProgramType::Int32);
        locals.set(CONTRACT_EXCEPTION, int32(11));
        locals.set("__click_exception", int32(13));
        for (name, expected) in [
            (source.clone(), 3),
            (BindingName::from("exception"), 7),
            (CONTRACT_EXCEPTION, 11),
            (BindingName::from("__click_exception"), 13),
        ] {
            assert_eq!(
                locals.get(&name).unwrap().native().as_ref(),
                &int32(expected)
            );
            assert_eq!(locals.resolve_binding(&name), name);
        }
        assert_eq!(locals.active_source_name(&CONTRACT_EXCEPTION), None);
        assert_eq!(CONTRACT_EXCEPTION.named(), None);
        assert_eq!(CONTRACT_EXCEPTION.to_string(), "exception");
        let result_slot = Memory::local_pointer(CONTRACT_EXCEPTION);
        assert_eq!(result_slot.block, PointerBlock::ContractException);
        assert!(
            result_slot
                .block
                .proven_distinct(&PointerBlock::ContractResult)
        );
        for binding in [
            source,
            BindingName::from("exception"),
            BindingName::from("__click_exception"),
        ] {
            assert!(
                result_slot
                    .block
                    .proven_distinct(&Memory::local_pointer(binding).block)
            );
        }
    }

    #[test]
    fn declaration_identity_is_separate_from_spelling_and_program_metadata() {
        let owner = LocalFunctionId::new(Some("unit.c".into()), "f".into());
        let first = local(&owner, 0, "x", 1);
        let renamed = local(&owner, 0, "y", 2);
        assert_eq!(first, renamed);
        assert_ne!(
            BindingDeclaration::from(first.clone()),
            BindingDeclaration::from(renamed)
        );
        assert_ne!(first, local(&owner, 1, "x", 1));
        assert_ne!(
            first,
            LocalBindingId::new(owner, true, 0, Some("x".into())).into()
        );
    }

    #[test]
    fn lexical_lookup_and_logical_binders_keep_exact_declarations() {
        let owner = LocalFunctionId::new(None, "f".into());
        let outer = local(&owner, 1, "x", 1);
        // Declaration introduction order need not be lexical nesting order,
        // for example when a GNU initializer declares another object.
        let inner = local(&owner, 0, "x", 2);
        let mut locals = LocalEnvironment::new();
        locals.set(&outer, int32(3));
        locals.set(&inner, int32(7));
        assert_eq!(locals.get("x").unwrap().native().as_ref(), &int32(7));
        assert_eq!(locals.get(&outer).unwrap().native().as_ref(), &int32(3));
        locals.bind_logical_typed("x", int32(11), ProgramType::Int32);
        assert_eq!(locals.get("x").unwrap().native().as_ref(), &int32(11));
        assert_eq!(locals.get(&inner).unwrap().native().as_ref(), &int32(7));
        locals.remove("x");
        assert_eq!(locals.get("x").unwrap().native().as_ref(), &int32(7));
        locals.remove(&inner);
        assert_eq!(locals.get("x").unwrap().native().as_ref(), &int32(3));
    }

    #[test]
    fn source_declarations_and_execution_storage_instances_are_distinct() {
        let owner = LocalFunctionId::new(None, "f".into());
        let binding = local(&owner, 0, "x", 1);
        let same_name_elsewhere = local(&LocalFunctionId::new(None, "g".into()), 0, "x", 1);
        let addresses = [
            Memory::local_pointer(&binding),
            Memory::value_parameter_pointer(&binding),
            Memory::local_lifetime_pointer(1, &binding),
            Memory::local_lifetime_pointer(2, &binding),
            Memory::frame_local_pointer(1, &binding),
            Memory::frame_local_pointer(2, &binding),
            Memory::local_pointer(same_name_elsewhere),
        ];
        for (index, address) in addresses.iter().enumerate() {
            for other in &addresses[index + 1..] {
                assert!(address.block.proven_distinct(&other.block));
            }
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    use super::*;
    include!("../../scaling_tests/kernel/primitives/bindings.rs");
}
