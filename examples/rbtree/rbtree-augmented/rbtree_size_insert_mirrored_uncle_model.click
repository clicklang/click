arithmetic "integer";

// Mirrored nonempty black middle and uncle subtrees retain arbitrary descendants.
// The in-order theorem leaves every descendant sequence symbolic.
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_model.click";

function sized_mirrored_context_uncle_before(g: struct rb_node*, p: struct rb_node*, m: struct rb_node*, u: struct rb_node*, n: struct rb_node*, above: struct rb_node*, nv: int32, pv: int32, gv: int32, mv: int32, uv: int32, left: SizedTree, right: SizedTree, middle_left: SizedTree, middle_right: SizedTree, uncle_left: SizedTree, uncle_right: SizedTree) -> SizedTree {
    SizedTree::Node(g, above, Color::Black, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), SizedTree::Node(n, p, Color::Red, nv, left, right)))
}

function sized_mirrored_context_uncle_after(g: struct rb_node*, p: struct rb_node*, m: struct rb_node*, u: struct rb_node*, n: struct rb_node*, above: struct rb_node*, left: SizedTree, right: SizedTree, middle_left: SizedTree, middle_right: SizedTree, uncle_left: SizedTree, uncle_right: SizedTree) -> RbTree {
    RbTree::Node(p, above, Color::Black, RbTree::Node(g, p, Color::Red, RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right)), RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right))), RbTree::Node(n, p, Color::Red, sized_shape(left), sized_shape(right)))
}

// The rotation preserves every identity and its in-order position.
theorem sized_mirrored_context_uncle_rotation_preserves_inorder(g: struct rb_node*, p: struct rb_node*, m: struct rb_node*, u: struct rb_node*,
        node: struct rb_node*, above: struct rb_node*, nv: int32, pv: int32, gv: int32, mv: int32, uv: int32,
        left: SizedTree, right: SizedTree, middle_left: SizedTree, middle_right: SizedTree, uncle_left: SizedTree, uncle_right: SizedTree) {
    ensures rb_inorder(sized_mirrored_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right))
        == rb_inorder(sized_shape(sized_mirrored_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right))) by {
        unfold(sized_mirrored_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
        unfold(sized_shape(SizedTree::Node(g, above, Color::Black, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), SizedTree::Node(node, p, Color::Red, nv, left, right)))));
        unfold(sized_shape(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), SizedTree::Node(node, p, Color::Red, nv, left, right))));
        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right)));
        unfold(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
        unfold(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
        unfold(sized_mirrored_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right));
        unfold(rb_inorder(RbTree::Node(g, above, Color::Black, RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right)), RbTree::Node(p, g, Color::Red, RbTree::Node(m, p, Color::Black, sized_shape(middle_left), sized_shape(middle_right)), RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right))))));
        unfold(rb_inorder(RbTree::Node(p, g, Color::Red, RbTree::Node(m, p, Color::Black, sized_shape(middle_left), sized_shape(middle_right)), RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right)))));
        unfold(rb_inorder(RbTree::Node(p, above, Color::Black, RbTree::Node(g, p, Color::Red, RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right)), RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right))), RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right)))));
        unfold(rb_inorder(RbTree::Node(g, p, Color::Red, RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right)), RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right)))));
        unfold(rb_inorder(RbTree::Node(m, p, Color::Black, sized_shape(middle_left), sized_shape(middle_right))));
        unfold(rb_inorder(RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right))));
        apply(list::append_associative(rb_inorder(RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right))), List::Cons(g, list::append(rb_inorder(sized_shape(middle_left)), List::Cons(m, rb_inorder(sized_shape(middle_right))))), List::Cons(p, rb_inorder(RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right))))));
        rewrite(list::append(list::append(rb_inorder(RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right))), List::Cons(g, list::append(rb_inorder(sized_shape(middle_left)), List::Cons(m, rb_inorder(sized_shape(middle_right)))))), List::Cons(p, rb_inorder(RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right))))) == list::append(rb_inorder(RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right))), list::append(List::Cons(g, list::append(rb_inorder(sized_shape(middle_left)), List::Cons(m, rb_inorder(sized_shape(middle_right))))), List::Cons(p, rb_inorder(RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right)))))));
        unfold(list::append(List::Cons(g, list::append(rb_inorder(sized_shape(middle_left)), List::Cons(m, rb_inorder(sized_shape(middle_right))))), List::Cons(p, rb_inorder(RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right))))));
        normalize();
    }
}
