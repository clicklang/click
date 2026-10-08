import "rbtree_erase_child.click";

theorem immediate_successor_child(successor: struct rb_node*, child: struct rb_node*, above: struct
    rb_node*) {
    ensures is_rb_root(plug(rb_min_context(RbTree::Node(successor, above, Color::Black, RbTree::Empty,
        RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty)), Context::Top),
        rb_reparent(rb_recolor(RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty),
        Color::Black), above))) == 1 by {
        have is_rb(RbTree::Node(successor, above, Color::Black, RbTree::Empty, RbTree::Node(child,
            successor, Color::Red, RbTree::Empty, RbTree::Empty))) == 1 by {
            unfold(is_rb(RbTree::Node(successor, above, Color::Black, RbTree::Empty, RbTree::Node(child,
                successor, Color::Red, RbTree::Empty, RbTree::Empty))));
            unfold(black_height(RbTree::Node(successor, above, Color::Black, RbTree::Empty,
                RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty))));
            unfold(rb_root_black(RbTree::Node(successor, above, Color::Black, RbTree::Empty,
                RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty))));
            unfold(is_rb(RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty)));
            unfold(black_height(RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty)));
            unfold(rb_root_black(RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty)));
            unfold(is_rb(RbTree::Empty));
            unfold(black_height(RbTree::Empty));
            unfold(rb_root_black(RbTree::Empty));
            normalize();
        }
        have ctx_rb(Context::Top, black_height(RbTree::Node(successor, above, Color::Black, RbTree::Empty,
            RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty))),
            rb_color(RbTree::Node(successor, above, Color::Black, RbTree::Empty, RbTree::Node(child,
            successor, Color::Red, RbTree::Empty, RbTree::Empty)))) == 1 by {
            unfold(ctx_rb(Context::Top, black_height(RbTree::Node(successor, above, Color::Black,
                RbTree::Empty, RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty))),
                rb_color(RbTree::Node(successor, above, Color::Black, RbTree::Empty, RbTree::Node(child,
                successor, Color::Red, RbTree::Empty, RbTree::Empty)))));
            unfold(rb_color(RbTree::Node(successor, above, Color::Black, RbTree::Empty, RbTree::Node(child,
                successor, Color::Red, RbTree::Empty, RbTree::Empty))));
            unfold(color_black(Color::Black)); normalize();
        }
        have rb_minimum(RbTree::Node(successor, above, Color::Black, RbTree::Empty, RbTree::Node(child,
            successor, Color::Red, RbTree::Empty, RbTree::Empty))) ==
        RbMinimum::Found(successor, Color::Black, RbTree::Node(child, successor, Color::Red, RbTree::Empty,
            RbTree::Empty)) by {
            unfold(rb_minimum(RbTree::Node(successor, above, Color::Black, RbTree::Empty,
                RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty)))); normalize();
        }
        have not(RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty) == RbTree::Empty)
            by { normalize(); }
        apply(rb_minimum_child_blackens_without_deficit(RbTree::Node(successor, above, Color::Black,
            RbTree::Empty, RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty)),
            Context::Top, successor, Color::Black, RbTree::Node(child, successor, Color::Red, RbTree::Empty,
            RbTree::Empty), above));
        assumption();
    }
}

theorem deep_successor_child(successor: struct rb_node*, child: struct rb_node*, above: struct rb_node*, r:
    struct rb_node*, far: struct rb_node*) {
    ensures is_rb_root(plug(rb_min_context(RbTree::Node(r, above, Color::Black, RbTree::Node(successor, r,
        Color::Black, RbTree::Empty, RbTree::Node(child, successor, Color::Red, RbTree::Empty,
        RbTree::Empty)), RbTree::Node(far, r, Color::Black, RbTree::Empty, RbTree::Empty)), Context::Top),
        rb_reparent(rb_recolor(RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty),
        Color::Black), r))) == 1 by {
        have is_rb(RbTree::Node(r, above, Color::Black, RbTree::Node(successor, r, Color::Black,
            RbTree::Empty, RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty)),
            RbTree::Node(far, r, Color::Black, RbTree::Empty, RbTree::Empty))) == 1 by {
            unfold(is_rb(RbTree::Node(r, above, Color::Black, RbTree::Node(successor, r, Color::Black,
                RbTree::Empty, RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty)),
                RbTree::Node(far, r, Color::Black, RbTree::Empty, RbTree::Empty))));
            unfold(black_height(RbTree::Node(r, above, Color::Black, RbTree::Node(successor, r,
                Color::Black, RbTree::Empty, RbTree::Node(child, successor, Color::Red, RbTree::Empty,
                RbTree::Empty)), RbTree::Node(far, r, Color::Black, RbTree::Empty, RbTree::Empty))));
            unfold(rb_root_black(RbTree::Node(r, above, Color::Black, RbTree::Node(successor, r,
                Color::Black, RbTree::Empty, RbTree::Node(child, successor, Color::Red, RbTree::Empty,
                RbTree::Empty)), RbTree::Node(far, r, Color::Black, RbTree::Empty, RbTree::Empty))));
            unfold(is_rb(RbTree::Node(successor, r, Color::Black, RbTree::Empty, RbTree::Node(child,
                successor, Color::Red, RbTree::Empty, RbTree::Empty))));
            unfold(black_height(RbTree::Node(successor, r, Color::Black, RbTree::Empty, RbTree::Node(child,
                successor, Color::Red, RbTree::Empty, RbTree::Empty))));
            unfold(rb_root_black(RbTree::Node(successor, r, Color::Black, RbTree::Empty, RbTree::Node(child,
                successor, Color::Red, RbTree::Empty, RbTree::Empty))));
            unfold(is_rb(RbTree::Node(far, r, Color::Black, RbTree::Empty, RbTree::Empty)));
            unfold(black_height(RbTree::Node(far, r, Color::Black, RbTree::Empty, RbTree::Empty)));
            unfold(rb_root_black(RbTree::Node(far, r, Color::Black, RbTree::Empty, RbTree::Empty)));
            unfold(is_rb(RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty)));
            unfold(black_height(RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty)));
            unfold(rb_root_black(RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty)));
            unfold(is_rb(RbTree::Empty));
            unfold(black_height(RbTree::Empty));
            unfold(rb_root_black(RbTree::Empty));
            normalize();
        }
        have ctx_rb(Context::Top, black_height(RbTree::Node(r, above, Color::Black, RbTree::Node(successor,
            r, Color::Black, RbTree::Empty, RbTree::Node(child, successor, Color::Red, RbTree::Empty,
            RbTree::Empty)), RbTree::Node(far, r, Color::Black, RbTree::Empty, RbTree::Empty))),
            rb_color(RbTree::Node(r, above, Color::Black, RbTree::Node(successor, r, Color::Black,
            RbTree::Empty, RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty)),
            RbTree::Node(far, r, Color::Black, RbTree::Empty, RbTree::Empty)))) == 1 by {
            unfold(ctx_rb(Context::Top, black_height(RbTree::Node(r, above, Color::Black,
                RbTree::Node(successor, r, Color::Black, RbTree::Empty, RbTree::Node(child, successor,
                Color::Red, RbTree::Empty, RbTree::Empty)), RbTree::Node(far, r, Color::Black,
                RbTree::Empty, RbTree::Empty))), rb_color(RbTree::Node(r, above, Color::Black,
                RbTree::Node(successor, r, Color::Black, RbTree::Empty, RbTree::Node(child, successor,
                Color::Red, RbTree::Empty, RbTree::Empty)), RbTree::Node(far, r, Color::Black,
                RbTree::Empty, RbTree::Empty)))));
            unfold(rb_color(RbTree::Node(r, above, Color::Black, RbTree::Node(successor, r, Color::Black,
                RbTree::Empty, RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty)),
                RbTree::Node(far, r, Color::Black, RbTree::Empty, RbTree::Empty))));
            unfold(color_black(Color::Black)); normalize();
        }
        have rb_minimum(RbTree::Node(r, above, Color::Black, RbTree::Node(successor, r, Color::Black,
            RbTree::Empty, RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty)),
            RbTree::Node(far, r, Color::Black, RbTree::Empty, RbTree::Empty))) ==
        RbMinimum::Found(successor, Color::Black, RbTree::Node(child, successor, Color::Red, RbTree::Empty,
            RbTree::Empty)) by {
            unfold(rb_minimum(RbTree::Node(r, above, Color::Black, RbTree::Node(successor, r, Color::Black,
                RbTree::Empty, RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty)),
                RbTree::Node(far, r, Color::Black, RbTree::Empty, RbTree::Empty))));
            unfold(rb_minimum(RbTree::Node(successor, r, Color::Black, RbTree::Empty, RbTree::Node(child,
                successor, Color::Red, RbTree::Empty, RbTree::Empty)))); normalize();
        }
        have not(RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty) == RbTree::Empty)
            by { normalize(); }
        apply(rb_minimum_child_blackens_without_deficit(RbTree::Node(r, above, Color::Black,
            RbTree::Node(successor, r, Color::Black, RbTree::Empty, RbTree::Node(child, successor,
            Color::Red, RbTree::Empty, RbTree::Empty)), RbTree::Node(far, r, Color::Black, RbTree::Empty,
            RbTree::Empty)), Context::Top, successor, Color::Black, RbTree::Node(child, successor,
            Color::Red, RbTree::Empty, RbTree::Empty), r));
        assumption();
    }
}
