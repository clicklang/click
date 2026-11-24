verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_metadata.click";

theorem sized_model_unique(a: SizedTree, b: SizedTree) {
    requires sized_counts_valid(a) == 1;
    requires sized_counts_valid(b) == 1;
    requires sized_shape(a) == sized_shape(b);
    ensures a == b by {
        let ih = induct(a);
        match a {
            SizedTree::Empty => {
                match b {
                    SizedTree::Empty => { known(); },
                    SizedTree::Node(bi, bp, bc, bv, bl, br) => {
                        have sized_shape(SizedTree::Empty) != sized_shape(b) by {
                            rewrite(b, SizedTree::Node(bi, bp, bc, bv, bl, br));
                            unfold(sized_shape(SizedTree::Empty)); unfold(sized_shape(SizedTree::Node(bi, bp, bc, bv, bl, br))); known();
                        }
                        contradiction(sized_shape(SizedTree::Empty) == sized_shape(b));
                    },
                }
            },
            SizedTree::Node(ai, ap, ac, av, al, ar) => {
                match b {
                    SizedTree::Empty => {
                        have sized_shape(SizedTree::Node(ai, ap, ac, av, al, ar)) != sized_shape(b) by {
                            rewrite(b, SizedTree::Empty);
                            unfold(sized_shape(SizedTree::Node(ai, ap, ac, av, al, ar))); unfold(sized_shape(SizedTree::Empty)); known();
                        }
                        contradiction(sized_shape(SizedTree::Node(ai, ap, ac, av, al, ar)) == sized_shape(b));
                    },
                    SizedTree::Node(bi, bp, bc, bv, bl, br) => {
                        unfold(sized_shape(SizedTree::Node(ai, ap, ac, av, al, ar))); unfold(sized_shape(SizedTree::Node(bi, bp, bc, bv, bl, br)));
                        have RbTree::Node(ai, ap, ac, sized_shape(al), sized_shape(ar)) == RbTree::Node(bi, bp, bc, sized_shape(bl), sized_shape(br)) by { known(); }
                        have ai == bi; have ap == bp; have ac == bc;
                        have sized_shape(al) == sized_shape(bl); have sized_shape(ar) == sized_shape(br);
                        apply(sized_valid_parts(ai, ap, ac, av, al, ar)); apply(sized_valid_parts(bi, bp, bc, bv, bl, br));
                        have bl == sized_left(b) by { rewrite(b, SizedTree::Node(bi, bp, bc, bv, bl, br)); unfold(sized_left(SizedTree::Node(bi, bp, bc, bv, bl, br))); known(); }
                        have br == sized_right(b) by { rewrite(b, SizedTree::Node(bi, bp, bc, bv, bl, br)); unfold(sized_right(SizedTree::Node(bi, bp, bc, bv, bl, br))); known(); }
                        apply(ih(al, sized_left(b))); apply(ih(ar, sized_right(b)));
                        have al == bl by { known(); }
                        have ar == br by { known(); }
                        have sized_value(al) == sized_value(bl) by { known(); }
                        have sized_value(ar) == sized_value(br) by { known(); }
                        have to_integer(sized_value(al)) == to_integer(sized_value(bl)) by { rewrite(al, bl); known(); }
                        have to_integer(sized_value(ar)) == to_integer(sized_value(br)) by { rewrite(ar, br); known(); }
                        have to_integer(av) == to_integer(bv) by {
                            close() using {
                                to_integer(av) == 1 + to_integer(sized_value(al)) + to_integer(sized_value(ar));
                                to_integer(bv) == 1 + to_integer(sized_value(bl)) + to_integer(sized_value(br));
                                to_integer(sized_value(al)) == to_integer(sized_value(bl));
                                to_integer(sized_value(ar)) == to_integer(sized_value(br));
                            };
                        }
                        solve();
                    },
                }
            },
        }
    }
}
