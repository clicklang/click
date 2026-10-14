verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
import "rbtree_size_metadata.click";

// Copying the cache cells must preserve the independently owned tree links.
contract void CopySizedStructure(struct rb_node* rb_old, struct rb_node* rb_new) {
    owns source_tree: rb_at(rb_old);
    owns target_tree: rb_at(rb_new);
    owns source: size_metadata(rb_old);
    owns target: size_metadata(rb_new);
    ensures source_tree.model == old(source_tree.model);
    ensures target_tree.model == old(target_tree.model);
    ensures source.value == old(source.value);
    ensures target.value == old(source.value);
}

theorem sized_copy_preserves_structure()
executes sized_copy(struct rb_node* rb_old, struct rb_node* rb_new) {
    ensures CopySizedStructure(&sized_copy) as {
        source_tree: source_tree, target_tree: target_tree, source: source, target: target
    } by {
        step(sized_copy(rb_old, rb_new), { source: source, target: target });
        simp();
    }
}
