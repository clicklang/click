import "rbtree_erase_splice.click";
import "rbtree_erase_root.click";

# The replacement child of the minimum has height zero. If nonempty,
# it is red and its parent is black; blackening it closes the hole.

theorem rb_minimum_child_valid(tree: RbTree, successor: struct rb_node*, min_color: Color, child: RbTree) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, min_color, child);
    requires is_rb(tree) == 1;
    ensures is_rb(child) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                have not(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color, child)) by {
                    unfold(rb_minimum(RbTree::Empty)); normalize();
                }
                contradiction(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color, child));
            }
            RbTree::Node(node, parent, color, left, right) => {
                if left == RbTree::Empty {
                    apply(rb_minimum_child_empty_left(node, parent, color, left, right, successor,
                        min_color, child));
                    extract(right == child);
                    apply(is_rb_node_right(node, parent, color, left, right));
                    rewrite(child == right); assumption();
                } else {
                    apply(rb_minimum_nonempty_left(node, parent, color, left, right));
                    have rb_minimum(left) == RbMinimum::Found(successor, min_color, child) by {
                        rewrite(rb_minimum(left) == rb_minimum(RbTree::Node(node, parent, color, left,
                            right)));
                        assumption();
                    }
                    apply(is_rb_node_left(node, parent, color, left, right));
                    apply(ih(left, successor, min_color, child)); assumption();
                }
            }
        }
    }
}

theorem rb_minimum_child_height(tree: RbTree, successor: struct rb_node*, min_color: Color, child: RbTree) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, min_color, child);
    requires is_rb(tree) == 1;
    ensures black_height(child) == Nat::Zero by {
        induct(tree) as ih {
            RbTree::Empty => {
                have not(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color, child)) by {
                    unfold(rb_minimum(RbTree::Empty)); normalize();
                }
                contradiction(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color, child));
            }
            RbTree::Node(node, parent, color, left, right) => {
                if left == RbTree::Empty {
                    apply(rb_minimum_child_empty_left(node, parent, color, left, right, successor,
                        min_color, child));
                    extract(right == child);
                    apply(is_rb_node_black_heights(node, parent, color, left, right));
                    rewrite(child == right);
                    rewrite(black_height(right) == black_height(left));
                    rewrite(left == RbTree::Empty);
                    unfold(black_height(RbTree::Empty)); normalize();
                } else {
                    apply(rb_minimum_nonempty_left(node, parent, color, left, right));
                    have rb_minimum(left) == RbMinimum::Found(successor, min_color, child) by {
                        rewrite(rb_minimum(left) == rb_minimum(RbTree::Node(node, parent, color, left,
                            right)));
                        assumption();
                    }
                    apply(is_rb_node_left(node, parent, color, left, right));
                    apply(ih(left, successor, min_color, child)); assumption();
                }
            }
        }
    }
}

theorem zero_frame_is_red(color: Color, height: Nat) {
    requires frame_black_height(color, height) == Nat::Zero;
    ensures color == Color::Red by {
        induct(color) as ih {
            Color::Red => { normalize(); }
            Color::Black => {
                have not(frame_black_height(Color::Black, height) == Nat::Zero) by {
                    unfold(frame_black_height(Color::Black, height)); normalize();
                }
                contradiction(frame_black_height(Color::Black, height) == Nat::Zero);
            }
        }
    }
}

theorem nonempty_zero_height_is_red(tree: RbTree) {
    requires not(tree == RbTree::Empty);
    requires black_height(tree) == Nat::Zero;
    ensures rb_color(tree) == Color::Red by {
        induct(tree) as ih {
            RbTree::Empty => {
                have RbTree::Empty == RbTree::Empty by { normalize(); }
                contradiction(RbTree::Empty == RbTree::Empty);
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(black_height_node_frame(node, parent, color, left, right));
                have frame_black_height(color, black_height(left)) == Nat::Zero by {
                    rewrite(frame_black_height(color, black_height(left)) == black_height(RbTree::Node(node,
                        parent, color, left, right))); assumption();
                }
                apply(zero_frame_is_red(color, black_height(left)));
                unfold(rb_color(RbTree::Node(node, parent, color, left, right))); assumption();
            }
        }
    }
}

theorem red_right_child_has_black_parent(node: struct rb_node*, parent: struct rb_node*, color: Color, left:
    RbTree, right: RbTree) {
    requires is_rb(RbTree::Node(node, parent, color, left, right)) == 1;
    requires rb_color(right) == Color::Red;
    ensures color == Color::Black by {
        induct(color) as ih {
            Color::Red => {
                apply(is_rb_red_node_right_child_is_black(node, parent, left, right));
                apply(rb_root_black_is_color_black(right));
                have not(rb_root_black(right) == 1) by {
                    rewrite(rb_root_black(right) == color_black(rb_color(right)));
                    rewrite(rb_color(right) == Color::Red);
                    unfold(color_black(Color::Red)); normalize();
                }
                contradiction(rb_root_black(right) == 1);
            }
            Color::Black => { normalize(); }
        }
    }
}

theorem rb_minimum_nonempty_child_parent_color(tree: RbTree, successor: struct rb_node*, min_color: Color,
    child: RbTree) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, min_color, child);
    requires is_rb(tree) == 1;
    requires not(child == RbTree::Empty);
    ensures min_color == Color::Black by {
        induct(tree) as ih {
            RbTree::Empty => {
                have not(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color, child)) by {
                    unfold(rb_minimum(RbTree::Empty)); normalize();
                }
                contradiction(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color, child));
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_minimum_child_height(RbTree::Node(node, parent, color, left, right), successor,
                    min_color, child));
                apply(nonempty_zero_height_is_red(child));
                if left == RbTree::Empty {
                    apply(rb_minimum_child_empty_left(node, parent, color, left, right, successor,
                        min_color, child));
                    extract(right == child);
                    extract(color == min_color);
                    have rb_color(right) == Color::Red by { rewrite(right == child); assumption(); }
                    apply(red_right_child_has_black_parent(node, parent, color, left, right));
                    rewrite(min_color == color); assumption();
                } else {
                    apply(rb_minimum_nonempty_left(node, parent, color, left, right));
                    have rb_minimum(left) == RbMinimum::Found(successor, min_color, child) by {
                        rewrite(rb_minimum(left) == rb_minimum(RbTree::Node(node, parent, color, left,
                            right)));
                        assumption();
                    }
                    apply(is_rb_node_left(node, parent, color, left, right));
                    apply(ih(left, successor, min_color, child)); assumption();
                }
            }
        }
    }
}


theorem blackening_red_adds_one(tree: RbTree) {
    requires rb_color(tree) == Color::Red;
    ensures black_height(rb_recolor(tree, Color::Black)) == Nat::Succ(black_height(tree)) by {
        induct(tree) as ih {
            RbTree::Empty => {
                have not(rb_color(RbTree::Empty) == Color::Red) by {
                    unfold(rb_color(RbTree::Empty)); normalize();
                }
                contradiction(rb_color(RbTree::Empty) == Color::Red);
            }
            RbTree::Node(node, parent, color, left, right) => {
                have color == Color::Red by {
                    unfold(rb_color(RbTree::Node(node, parent, color, left, right)));
                    rewrite(color == rb_color(RbTree::Node(node, parent, color, left, right)));
                        assumption();
                }
                rewrite(color == Color::Red);
                unfold(rb_recolor(RbTree::Node(node, parent, Color::Red, left, right), Color::Black));
                unfold(black_height(RbTree::Node(node, parent, Color::Black, left, right)));
                unfold(black_height(RbTree::Node(node, parent, Color::Red, left, right)));
                normalize();
            }
        }
    }
}

theorem black_color_is_black(color: Color) {
    requires color_black(color) == 1;
    ensures color == Color::Black by {
        induct(color) as ih {
            Color::Red => {
                have not(color_black(Color::Red) == 1) by { unfold(color_black(Color::Red)); normalize(); }
                contradiction(color_black(Color::Red) == 1);
            }
            Color::Black => { normalize(); }
        }
    }
}

theorem rb_minimum_child_blackens_without_deficit(tree: RbTree, up: Context, successor: struct rb_node*,
    min_color: Color, child: RbTree, parent: struct rb_node*) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, min_color, child);
    requires is_rb(tree) == 1;
    requires ctx_rb(up, black_height(tree), rb_color(tree)) == 1;
    requires not(child == RbTree::Empty);
    ensures is_rb_root(plug(rb_min_context(tree, up), rb_reparent(rb_recolor(child, Color::Black), parent)))
        == 1 by {
        apply(rb_minimum_child_valid(tree, successor, min_color, child));
        apply(rb_minimum_child_height(tree, successor, min_color, child));
        apply(nonempty_zero_height_is_red(child));
        apply(rb_minimum_nonempty_child_parent_color(tree, successor, min_color, child));
        apply(rb_min_context_child(tree, up, successor, min_color, child));
        apply(blackening_red_adds_one(child));
        apply(rb_blacken_reparent_is_rb_root(child, parent));
        apply(is_rb_root_is_rb(rb_reparent(rb_recolor(child, Color::Black), parent)));
        apply(rb_reparent_preserves_black_height(rb_recolor(child, Color::Black), parent));
        apply(is_rb_root_root_black(rb_reparent(rb_recolor(child, Color::Black), parent)));
        apply(rb_root_black_is_color_black(rb_reparent(rb_recolor(child, Color::Black), parent)));
        have black_height(rb_reparent(rb_recolor(child, Color::Black), parent)) == Nat::Succ(Nat::Zero) by {
            rewrite(black_height(rb_reparent(rb_recolor(child, Color::Black), parent)) ==
                black_height(rb_recolor(child, Color::Black)));
            rewrite(black_height(rb_recolor(child, Color::Black)) == Nat::Succ(black_height(child)));
            rewrite(black_height(child) == Nat::Zero); normalize();
        }
        have ctx_rb(rb_min_context(tree, up), Nat::Succ(Nat::Zero), Color::Black) == 1 by {
            unfold(frame_black_height(Color::Black, Nat::Zero));
            rewrite(Nat::Succ(Nat::Zero) == frame_black_height(Color::Black, Nat::Zero));
            rewrite(Color::Black == min_color); assumption();
        }
        have color_black(rb_color(rb_reparent(rb_recolor(child, Color::Black), parent))) == 1 by {
            rewrite(color_black(rb_color(rb_reparent(rb_recolor(child, Color::Black), parent))) ==
                rb_root_black(rb_reparent(rb_recolor(child, Color::Black), parent))); assumption();
        }
        apply(black_color_is_black(rb_color(rb_reparent(rb_recolor(child, Color::Black), parent))));
        have ctx_rb(rb_min_context(tree, up), black_height(rb_reparent(rb_recolor(child, Color::Black),
            parent)), rb_color(rb_reparent(rb_recolor(child, Color::Black), parent))) == 1 by {
            rewrite(black_height(rb_reparent(rb_recolor(child, Color::Black), parent)) ==
                Nat::Succ(Nat::Zero));
            rewrite(rb_color(rb_reparent(rb_recolor(child, Color::Black), parent)) == Color::Black);
            assumption();
        }
        apply(plug_rb_from_ctx_rb(rb_min_context(tree, up), rb_reparent(rb_recolor(child, Color::Black),
            parent)));
        assumption();
    }
}
