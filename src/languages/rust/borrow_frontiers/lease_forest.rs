//! Checked scalar lease births and common ending frontiers. Reference
//! aliases name one node; reborrows add a dependency edge. A reverse tree pass
//! propagates descendant uses, avoiding one whole-function scan per borrow.
use super::*;
use crate::kernel::{ScalarReferencePlanFamily, ScalarReferencePlanKey};
mod regions;

pub(in crate::languages::rust) struct CheckedBirth {
    pub parent: String,
    pub child: String,
    pub pointee: Type,
    pub key: ScalarReferencePlanKey,
}
pub(in crate::languages::rust) struct CheckedScope {
    pub family: std::sync::Arc<ScalarReferencePlanFamily>,
    pub join: usize,
    pub locals: BTreeMap<String, Type>,
}
pub(in crate::languages::rust) struct CheckedForest {
    pub scopes: BTreeMap<usize, CheckedScope>,
    pub births: BTreeMap<MirPoint, CheckedBirth>,
    pub endings: BTreeMap<MirPoint, Vec<ScalarReferencePlanKey>>,
}
struct Node {
    parent: Option<usize>,
    name: String,
    child: String,
    pointee: Type,
    birth: MirPoint,
    last: usize,
    path: usize,
}
fn scalar(ty: &Type) -> bool {
    matches!(
        ty,
        Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Usize | Type::Bool
    )
}
fn pointee(ty: &Type) -> bool {
    matches!(ty, Type::I32 | Type::U8 | Type::U16 | Type::U32)
}
fn touch(
    name: &str,
    point: usize,
    aliases: &BTreeMap<&str, usize>,
    nodes: &mut [Node],
    definitions: &BTreeMap<&str, usize>,
    projection: &regions::Projection<'_>,
) -> bool {
    if let Some(path) = definitions.get(name)
        && projection
            .frontier(*path, &projection.events[point])
            .is_none()
    {
        return false;
    }
    if let Some(node) = aliases.get(name) {
        nodes[*node].last = point;
    }
    true
}

fn value(
    expr: &E,
    point: usize,
    types: &BTreeMap<&str, &Type>,
    aliases: &BTreeMap<&str, usize>,
    nodes: &mut [Node],
    definitions: &BTreeMap<&str, usize>,
    projection: &regions::Projection<'_>,
) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    match expr {
        E::Integer { .. } | E::UnsignedInteger { .. } | E::Boolean { .. } => true,
        E::Local { name } => types.get(name.as_str()).is_some_and(|ty| scalar(ty)),
        E::Deref {
            reference,
            value_type,
        } => {
            let E::Local { name } = reference.as_ref() else {
                return false;
            };
            if !scalar(value_type)
                || !matches!(types.get(name.as_str()), Some(Type::Reference { pointee, .. }) if pointee.as_ref() == value_type)
            {
                return false;
            }
            touch(name, point, aliases, nodes, definitions, projection)
        }
        E::Binary { left, right, .. } => {
            value(left, point, types, aliases, nodes, definitions, projection)
                && value(right, point, types, aliases, nodes, definitions, projection)
        }
        E::IntegerFrom { value: inner, .. }
        | E::Cast { value: inner, .. }
        | E::Not { value: inner }
        | E::BitwiseNot { value: inner, .. } => {
            value(inner, point, types, aliases, nodes, definitions, projection)
        }
        _ => false,
    }
}

pub(in crate::languages::rust) fn certify(
    function: &Function,
    identity: Option<&str>,
    joins: &[usize],
) -> Option<CheckedForest> {
    let identity = identity?;
    let mir = function.mir.as_ref()?;
    let projection = regions::project(mir, joins)?;
    if function.return_type != Type::Unit && !scalar(&function.return_type) {
        return None;
    }
    let mut types = BTreeMap::new();
    let parameters: BTreeSet<_> = function
        .parameters
        .iter()
        .map(|p| p.name.as_str())
        .collect();
    for local in function.parameters.iter().chain(&mir.locals) {
        crate::instrumentation::record_deterministic_work(1);
        if types
            .insert(local.name.as_str(), &local.value_type)
            .is_some()
        {
            return None;
        }
        if !scalar(&local.value_type)
            && local.value_type != Type::Unit
            && !matches!(&local.value_type, Type::Reference { pointee: ty, .. } if pointee(ty))
        {
            return None;
        }
    }
    let family = ScalarReferencePlanFamily::new(identity, &function.name);
    let mut scopes: BTreeMap<usize, CheckedScope> = BTreeMap::new();
    let mut definitions: BTreeMap<&str, usize> = parameters.iter().map(|name| (*name, 0)).collect();
    let mut aliases = BTreeMap::new();
    let mut nodes: Vec<Node> = vec![];
    for (point, event) in projection.events.iter().enumerate() {
        crate::instrumentation::record_deterministic_work(1);
        let statement = match event.operation {
            regions::Operation::Statement(statement) => statement,
            regions::Operation::Condition(condition) => {
                if !value(
                    condition,
                    point,
                    &types,
                    &aliases,
                    &mut nodes,
                    &definitions,
                    &projection,
                ) {
                    return None;
                }
                continue;
            }
        };
        if let S::Assign {
            target: E::Local { name },
            ..
        } = statement
            && matches!(types.get(name.as_str()), Some(Type::Reference { .. }))
        {
            if definitions
                .get(name.as_str())
                .is_some_and(|path| *path != event.path)
            {
                return None;
            }
            definitions.insert(name.as_str(), event.path);
            if let Some((fork, join)) = projection.scope(event.path) {
                scopes
                    .entry(fork)
                    .or_insert_with(|| CheckedScope {
                        family: family.clone(),
                        join,
                        locals: BTreeMap::new(),
                    })
                    .locals
                    .insert(name.clone(), (*types[name.as_str()]).clone());
            }
        }
        match statement {
            S::Assign {
                target: E::Local { name: child },
                value: E::Borrow { place, value_type },
            } => {
                let Type::Reference {
                    mutable: true,
                    pointee: ty,
                } = value_type
                else {
                    return None;
                };
                let E::Deref {
                    reference,
                    value_type: addressed,
                } = place.as_ref()
                else {
                    return None;
                };
                let E::Local { name: parent } = reference.as_ref() else {
                    return None;
                };
                if !pointee(ty)
                    || ty.as_ref() != addressed
                    || parent == child
                    || types.get(child.as_str()).copied() != Some(value_type)
                    || types.get(parent.as_str()).copied() != Some(value_type)
                {
                    return None;
                }
                let parent_node = aliases.get(parent.as_str()).copied();
                if parent_node.is_none() && !parameters.contains(parent.as_str()) {
                    return None;
                }
                if !touch(
                    parent,
                    point,
                    &aliases,
                    &mut nodes,
                    &definitions,
                    &projection,
                ) {
                    return None;
                }
                aliases.insert(child.as_str(), nodes.len());
                nodes.push(Node {
                    parent: parent_node,
                    name: parent.clone(),
                    child: child.clone(),
                    pointee: ty.as_ref().clone(),
                    birth: event.source,
                    last: point,
                    path: event.path,
                });
            }
            S::Assign {
                target: E::Local { name },
                value: expr,
            } => {
                let ty = *types.get(name.as_str())?;
                if matches!(ty, Type::Reference { .. }) {
                    let E::Local { name: source } = expr else {
                        return None;
                    };
                    if types.get(source.as_str()).copied() != Some(ty) {
                        return None;
                    }
                    if !touch(
                        source,
                        point,
                        &aliases,
                        &mut nodes,
                        &definitions,
                        &projection,
                    ) {
                        return None;
                    }
                    match aliases.get(source.as_str()).copied() {
                        Some(node) => {
                            aliases.insert(name.as_str(), node);
                        }
                        None => {
                            aliases.remove(name.as_str());
                        }
                    }
                } else if !scalar(ty)
                    || !value(
                        expr,
                        point,
                        &types,
                        &aliases,
                        &mut nodes,
                        &definitions,
                        &projection,
                    )
                {
                    return None;
                }
            }
            S::Assign {
                target:
                    E::Deref {
                        reference,
                        value_type,
                    },
                value: expr,
            } => {
                let E::Local { name } = reference.as_ref() else {
                    return None;
                };
                if !scalar(value_type)
                    || !matches!(types.get(name.as_str()), Some(Type::Reference { mutable: true, pointee }) if pointee.as_ref() == value_type)
                    || !value(
                        expr,
                        point,
                        &types,
                        &aliases,
                        &mut nodes,
                        &definitions,
                        &projection,
                    )
                {
                    return None;
                }
                if !touch(name, point, &aliases, &mut nodes, &definitions, &projection) {
                    return None;
                }
            }
            S::BeginStorage { local } | S::EndStorage { local }
                if types.contains_key(local.as_str()) => {}
            _ => return None,
        }
    }
    // Children are born after their parent. Reverse order both computes each
    // subtree's last use and later emits shared-frontier ends innermost first.
    for index in (0..nodes.len()).rev() {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(parent) = nodes[index].parent {
            nodes[parent].last = nodes[parent].last.max(nodes[index].last);
        }
    }
    let mut births = BTreeMap::new();
    let mut endings: BTreeMap<MirPoint, Vec<_>> = BTreeMap::new();
    for node in nodes.into_iter().rev() {
        let end = projection.frontier(node.path, &projection.events[node.last])?;
        let key = ScalarReferencePlanKey {
            family: family.clone(),
            block: node.birth.block,
            borrow: node.birth.statement,
            end_block: end.block,
            end: end.statement,
        };
        endings.entry(end).or_default().push(key.clone());
        births.insert(
            node.birth,
            CheckedBirth {
                parent: node.name,
                child: node.child,
                pointee: node.pointee,
                key,
            },
        );
    }
    Some(CheckedForest {
        scopes,
        births,
        endings,
    })
}
