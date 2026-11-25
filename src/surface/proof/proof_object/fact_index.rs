//! Surface-only helpers adjacent to the kernel-owned proof fact store.

use super::*;

pub(in crate::surface::proof) fn collect_surface_conjunct_leaves(
    proposition: &SyntaxProposition,
    leaves: &mut Vec<SyntaxProposition>,
) {
    match proposition {
        SyntaxProposition::And(left, right) => {
            collect_surface_conjunct_leaves(left, leaves);
            collect_surface_conjunct_leaves(right, leaves);
        }
        leaf => leaves.push(leaf.clone()),
    }
}
