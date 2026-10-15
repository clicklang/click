//! Checked same-block scalar lease births and ending frontiers. Reference
//! aliases name one node; reborrows add a dependency edge. A reverse tree pass
//! propagates descendant uses, avoiding one whole-function scan per borrow.
use super::*;
use crate::kernel::{ScalarReferencePlanFamily, ScalarReferencePlanKey};

pub(in crate::languages::rust) struct CheckedBirth {
    pub parent: String,
    pub child: String,
    pub pointee: Type,
    pub key: ScalarReferencePlanKey,
}
pub(in crate::languages::rust) struct CheckedForest {
    pub births: BTreeMap<usize, CheckedBirth>,
    pub endings: BTreeMap<usize, Vec<ScalarReferencePlanKey>>,
}
struct Node {
    parent: Option<usize>,
    name: String,
    child: String,
    pointee: Type,
    birth: usize,
    last: usize,
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
fn touch(name: &str, point: usize, aliases: &BTreeMap<&str, usize>, nodes: &mut [Node]) {
    if let Some(node) = aliases.get(name) {
        nodes[*node].last = point;
    }
}
fn value(
    expr: &E,
    point: usize,
    types: &BTreeMap<&str, &Type>,
    aliases: &BTreeMap<&str, usize>,
    nodes: &mut [Node],
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
            touch(name, point, aliases, nodes);
            true
        }
        E::Binary { left, right, .. } => {
            value(left, point, types, aliases, nodes) && value(right, point, types, aliases, nodes)
        }
        E::IntegerFrom { value: inner, .. }
        | E::Cast { value: inner, .. }
        | E::Not { value: inner }
        | E::BitwiseNot { value: inner, .. } => value(inner, point, types, aliases, nodes),
        _ => false,
    }
}

pub(in crate::languages::rust) fn certify(
    function: &Function,
    identity: Option<&str>,
) -> Option<CheckedForest> {
    let identity = identity?;
    let mir = function.mir.as_ref()?;
    if mir.blocks.len() != 1 || !matches!(mir.blocks[0].terminator, T::Return) {
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
    let mut aliases = BTreeMap::new();
    let mut nodes: Vec<Node> = vec![];
    for (point, statement) in mir.blocks[0].statements.iter().enumerate() {
        crate::instrumentation::record_deterministic_work(1);
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
                touch(parent, point, &aliases, &mut nodes);
                aliases.insert(child.as_str(), nodes.len());
                nodes.push(Node {
                    parent: parent_node,
                    name: parent.clone(),
                    child: child.clone(),
                    pointee: ty.as_ref().clone(),
                    birth: point,
                    last: point,
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
                    touch(source, point, &aliases, &mut nodes);
                    match aliases.get(source.as_str()).copied() {
                        Some(node) => {
                            aliases.insert(name.as_str(), node);
                        }
                        None => {
                            aliases.remove(name.as_str());
                        }
                    }
                } else if !scalar(ty) || !value(expr, point, &types, &aliases, &mut nodes) {
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
                    || !value(expr, point, &types, &aliases, &mut nodes)
                {
                    return None;
                }
                touch(name, point, &aliases, &mut nodes);
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
    let family = ScalarReferencePlanFamily::new(identity, &function.name);
    let mut births = BTreeMap::new();
    let mut endings: BTreeMap<usize, Vec<_>> = BTreeMap::new();
    for node in nodes.into_iter().rev() {
        let key = ScalarReferencePlanKey {
            family: family.clone(),
            block: 0,
            borrow: node.birth,
            end: node.last + 1,
        };
        endings.entry(key.end).or_default().push(key.clone());
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
    Some(CheckedForest { births, endings })
}
