arithmetic "integer";

verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_metadata.click";

theorem sized_model_unique(a: SizedTree, b: SizedTree) {
    requires sized_counts_valid(a) == 1;
    requires sized_counts_valid(b) == 1;
    requires sized_shape(a) == sized_shape(b);
    ensures a == b by {
        induct(a) as ih {
            SizedTree::Empty => {
                match b {
                    SizedTree::Empty => { assumption(); },
                    SizedTree::Node(bi, bp, bc, bv, bl, br) => {
                        have sized_shape(SizedTree::Empty) != sized_shape(b) by {
                            rewrite(b == SizedTree::Node(bi, bp, bc, bv, bl, br));
                            unfold(sized_shape(SizedTree::Empty)); unfold(sized_shape(SizedTree::Node(bi, bp, bc, bv, bl, br))); normalize();
                        }
                        contradiction(sized_shape(SizedTree::Empty) == sized_shape(b));
                    },
                }
            },
            SizedTree::Node(ai, ap, ac, av, al, ar) => {
                match b {
                    SizedTree::Empty => {
                        have sized_shape(SizedTree::Node(ai, ap, ac, av, al, ar)) != sized_shape(b) by {
                            rewrite(b == SizedTree::Empty);
                            unfold(sized_shape(SizedTree::Node(ai, ap, ac, av, al, ar))); unfold(sized_shape(SizedTree::Empty)); normalize();
                        }
                        contradiction(sized_shape(SizedTree::Node(ai, ap, ac, av, al, ar)) == sized_shape(b));
                    },
                    SizedTree::Node(bi, bp, bc, bv, bl, br) => {
                        unfold(sized_shape(SizedTree::Node(ai, ap, ac, av, al, ar))); unfold(sized_shape(SizedTree::Node(bi, bp, bc, bv, bl, br)));
                        have RbTree::Node(ai, ap, ac, sized_shape(al), sized_shape(ar)) == RbTree::Node(bi, bp, bc, sized_shape(bl), sized_shape(br)) by { assumption(); }
                        extract(ai == bi); extract(ap == bp); extract(ac == bc);
                        extract(sized_shape(al) == sized_shape(bl)); extract(sized_shape(ar) == sized_shape(br));
                        apply(sized_valid_parts(ai, ap, ac, av, al, ar)); apply(sized_valid_parts(bi, bp, bc, bv, bl, br)) using { sized_counts_valid(SizedTree::Node(bi, bp, bc, bv, bl, br)) == 1; };
                        have bl == sized_left(b) by { rewrite(b == SizedTree::Node(bi, bp, bc, bv, bl, br)); unfold(sized_left(SizedTree::Node(bi, bp, bc, bv, bl, br))); normalize(); }
                        have br == sized_right(b) by { rewrite(b == SizedTree::Node(bi, bp, bc, bv, bl, br)); unfold(sized_right(SizedTree::Node(bi, bp, bc, bv, bl, br))); normalize(); }
                        apply(ih(al, sized_left(b))); apply(ih(ar, sized_right(b)));
                        have al == bl by { assumption(); }
                        have ar == br by { assumption(); }
                        have sized_value(al) == sized_value(bl) by { assumption(); }
                        have sized_value(ar) == sized_value(br) by { assumption(); }
                        have to_integer(sized_value(al)) == to_integer(sized_value(bl)) by { rewrite(al == bl); normalize(); }
                        have to_integer(sized_value(ar)) == to_integer(sized_value(br)) by { rewrite(ar == br); normalize(); }
                        have to_integer(av) == to_integer(bv) by {
                            arithmetic() using {
                                to_integer(av) == 1 + to_integer(sized_value(al)) + to_integer(sized_value(ar));
                                to_integer(bv) == 1 + to_integer(sized_value(bl)) + to_integer(sized_value(br));
                                to_integer(sized_value(al)) == to_integer(sized_value(bl));
                                to_integer(sized_value(ar)) == to_integer(sized_value(br));
                            };
                        }
                        apply(click::integer::int32_to_integer_equal_implies_equal(av, bv)) using { to_integer(av) == to_integer(bv); };
                        simp();
                    },
                }
            },
        }
    }
}
